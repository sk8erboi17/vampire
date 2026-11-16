/* MODULO engine_derivatives: derivate: dimostrarle, calcolarle, usarle negli
 * studi di funzione (capitolo 27).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_derivatives.h,
 * e il resto è static. */
#include "engine_derivatives.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"
#include "engine_intervals.h"
#include "engine_quantifiers.h"
#include "engine_sign_tables.h"
#include "engine_explanation.h"
#include "engine_sequences.h"

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
Node *derivatives_expanded(Node *tree);
void formula_derivatives_expanded(Formula *f);
const char *derivative_doubt(const Formula *thesis);
_Thread_local int derivative_signs;

/* 1 se derivative_doubt() ha trovato un estremo del dominio di una funzione
 * in cui la derivata (da tutte e due le parti) non esiste: il verdetto lo
 * dice, perché chi conta la derivata da una parte sola leggerebbe in un
 * altro modo la risposta. */
_Thread_local int derivative_edges;
const char *const DERIVATIVE_EDGES = "negli estremi del dominio la derivata, che chiede la funzione definita da tutte e due le parti, non c'è";

/* =============================================================================
 * 27. DERIVATE: DIMOSTRARLE, CALCOLARLE, USARLE NEGLI STUDI DI FUNZIONE
 * ============================================================================
 *
 * A che cosa serve. "La derivata n-esima di sin x è sin(x + n pi/2)"; "la
 * derivata n-esima di ln x è (-1)^{n-1} (n-1)! / x^n, per n >= 1"; "la
 * derivata di x^2 tan x è x (sin 2x + x) / cos^2 x". L'enunciato arriva
 * nella notazione di parse_derivative_statement(): il segno di derivata, la
 * funzione f, il segno di uguale, una formula g(n, x). Lo stesso segno serve
 * in altri due modi, ognuno nel suo paragrafo:
 *
 *   27j. dentro un'espressione, per gli studi di funzione: il segno diventa
 *        la derivata, e la tabella dei segni (18p) decide l'enunciato;
 *   27k. senza il segno di uguale, come richiesta: la derivata si calcola,
 *        si scrive e si rilegge;
 *   27l. negli studi, i punti in cui la funzione è definita ma le regole
 *        non ne danno la derivata.
 *
 * E il certificato, 27m, che le derivate dimostrate o calcolate portano a
 * checker.c, e che il capitolo 30 usa per le primitive e gli integrali. E
 * la spiegazione di una derivata richiesta, 27n: una riga per regola, per
 * il documento (capitolo 40).
 *
 * IL TEOREMA
 *
 * Sia n0 >= 0. Se
 *
 *   27a. la derivata di ordine n0 di f è g(n0, x);
 *   27b. per ogni intero n >= n0 la derivata rispetto a x di g(n, x) è
 *        g(n + 1, x);
 *
 * allora la derivata di ordine n di f è g(n, x) per ogni n >= n0. È
 * un'induzione su n: la derivata di ordine n + 1 è la derivata di quella di
 * ordine n, che per ipotesi è g(n, x), e 27b dice quanto vale. Come ogni
 * verdetto del capitolo 13, vale dove le espressioni sono definite.
 *
 * COME SI DERIVA
 *
 * derive() applica le regole di derivazione all'albero di un'espressione, un
 * nodo alla volta, senza cercare nulla. u e v dipendono da x, c no:
 *
 *   27c. c' = 0, x' = 1, (u + v)' = u' + v', (-u)' = -u';
 *   27d. (u v)' = u' v + u v',   (u / v)' = (u' v - u v') / v^2;
 *   27e. (u^c)' = c u^{c-1} u' con c intero, e c u^c u' / u con ogni
 *        altro c; (c^u)' = c^u ln(c) u', con ln(e) = 1; con x nella base e
 *        nell'esponente u^v = e^{v ln u}, e quindi
 *        (u^v)' = u^v (v' ln u + v u' / u), dove u > 0;
 *   27f. la regola della catena, f(u)' = f'(u) u', con sin' = cos,
 *        cos' = -sin, tan' = 1/cos^2, cot' = -1/sin^2, ln' = 1/u,
 *        arctan' = 1/(1 + u^2), arccot' = -1/(1 + u^2),
 *        arcsin' = 1/sqrt(1 - u^2), arccos' = -1/sqrt(1 - u^2), per la
 *        radice m-esima r di u r' = r u' / (m u), per il valore assoluto
 *        |u|' = u' u / |u| e (ln|u|)' = u'/u, e log_b u = ln u / ln b
 *        anche con x nella base b;
 *   27g. la derivata di una somma con \sum è la somma delle derivate.
 *
 * La lettera e è il numero di Nepero: senza questo e^x non avrebbe per
 * derivata se stessa. Ciò che non rientra (x nell'indice di una radice, un
 * prodotto con \prod, un fattoriale di x) è NON SUPPORTATO.
 *
 * Dove valgono le formule. Ogni regola dà una formula che ha un valore solo
 * dove la funzione è derivabile, e lì vale la derivata: è ciò che permette
 * di usare le derivate dentro un'espressione (27j). Per questo alcune sono
 * scritte in un modo che sembra più lungo del necessario:
 *
 *   - c u^c u' / u, e non c u^{c-1} u', quando c non è intero: u^{3/2} è
 *     definita in u = 0 e lì c u^{c-1} = 0, ma u^{3/2} non è definita per
 *     u < 0, quindi in u = 0 la derivata (da tutte e due le parti) non
 *     esiste; la divisione per u la toglie. È lo stesso motivo della
 *     divisione per m u nella radice;
 *   - u' u / |u| non ha valore dove u = 0, dove |u| di solito non è
 *     derivabile (a volte lo è, come |x^3|: di questi punti si occupa
 *     27l); 1/sqrt(1 - u^2) non ce l'ha dove u = 1 o u = -1, gli estremi
 *     del dominio dell'arcoseno;
 *   - (u^v)' contiene ln u, che chiede u > 0: è la convenzione dei libri,
 *     u^v = e^{v ln u}, e il verdetto la dice.
 *
 * Fatte le derivate, 27a e 27b non contengono più il segno di derivata:
 * sono un'uguaglianza tra due espressioni in x, e un'identità in n e x che
 * l'induzione del capitolo 13 dimostra con tutti i suoi controlli.
 *
 * I CONTROLLI INDIPENDENTI
 *
 * Le regole di derivazione sono scritte una volta sola, in derive(): una
 * regola sbagliata darebbe una dimostrazione con tutti i passi in ordine e
 * la conclusione falsa. Per questo ogni derivata che derive() calcola viene
 * ricontrollata con un metodo che non usa le sue regole, in sei punti x0 e
 * con dei numeri al posto delle altre lettere, attraverso gli intervalli
 * del capitolo 24:
 *
 *   27h. La serie di Taylor della funzione in x0, calcolata con gli
 *        intervalli dall'albero della funzione stessa (vedi "Le derivate con
 *        i numeri", più sotto), dà un intervallo che contiene di sicuro la
 *        derivata k-esima vera in x0. Lo si confronta con il valore in x0
 *        della derivata k-esima calcolata da derive(). Se i due intervalli
 *        non si toccano, una regola è sbagliata: è un errore del programma,
 *        unjustified_steps sale e il verdetto non è né DIMOSTRATO né FALSO.
 *        Se i due numeri distano di sicuro meno di AGREEMENT, la derivata è
 *        confermata in quel punto; altrimenti, lì, non si sa. Ogni derivata
 *        fino all'ordine del caso base deve essere confermata in almeno un
 *        punto, e così la derivata della formula, nel passo 27b, per
 *        n = n0 e n = n0 + 1.
 *   27i. Le derivate di f di ordine n0, n0 + 1, ... vengono confrontate con
 *        la formula: è la strada che non passa dall'induzione. Il verdetto è
 *        FALSO con quell'n solo se in un punto x0 la derivata delle regole è
 *        confermata (27h) e la formula è di sicuro diversa sia da lei sia
 *        da quella della serie di Taylor. Così un FALSO non poggia su una
 *        regola che nessuno ha controllato in quel punto: per dire il falso
 *        dovrebbero sbagliare allo stesso modo, nello stesso punto, due
 *        conti scritti in modo diverso. Se la formula è di sicuro diversa da
 *        uno solo dei due, il verdetto è NON DIMOSTRATO. DIMOSTRATO chiede
 *        che in nessun punto la formula sia smentita, e che in almeno un
 *        punto, per almeno un ordine, la formula e la serie di Taylor
 *        coincidano.
 *
 * Che cosa questi controlli non danno: una prova che le regole sono giuste
 * dappertutto. Due funzioni diverse possono coincidere in sei punti. Ma una
 * regola sbagliata dà una derivata diversa da quella vera quasi ovunque (le
 * funzioni trattate sono analitiche dove sono definite e derivabili, e due
 * funzioni analitiche diverse su un intervallo coincidono lì solo in punti
 * isolati), e sei punti scelti senza guardare le regole bastano a vederla,
 * salvo coincidenze. Un FALSO dice invece una cosa precisa, che gli
 * intervalli garantiscono se le ricorrenze di 27h sono scritte giuste (ed è
 * per questo che vi devono concordare anche le regole): in quel punto, con
 * quei valori delle altre lettere, la derivata vera non è la formula.
 *
 * IL CERTIFICATO (27m)
 *
 * Il verdetto DIMOSTRATO, o RISOLTO per una richiesta, porta un certificato
 * per checker.c (capitolo 13), che deriva la funzione da sé, con regole sue
 * scritte un'altra volta, e decide con la sua algebra esatta che la
 * differenza dalla formula è zero. Il verificatore conosce funzioni
 * razionali, esponenziali, logaritmi, seni, coseni, arcotangenti, radici e
 * valori assoluti, non arcoseno e arcocoseno: dove non arriva il verdetto
 * dice perché il certificato manca. Gli studi di funzione (27j), decisi con
 * la tabella dei segni, non hanno ancora un certificato: servirebbe insieme
 * quello della tabella e quello di ogni derivata espansa.
 */

/* Il motivo con cui prove_derivative() rifiuta ciò che non è scritto come una
 * derivata. Ha un nome perché prove() (capitolo 20) lo riconosce e lo
 * sostituisce con il motivo più preciso del lettore, se c'è. */
const char *const NOT_A_DERIVATIVE = "l'enunciato non comincia con il segno di derivata";

/* Ritorna tree con i figli a, b e c al posto dei suoi: tree stesso se sono
 * gli stessi, altrimenti una copia con gli altri campi uguali. Non copiare
 * ciò che non cambia conta: la tabella dei segni riconosce come uno solo un
 * valore assoluto che un albero raggiunge per due strade, dal suo indirizzo
 * (abs_collect()). */
static Node *node_rebuilt(const Node *tree, Node *a, Node *b, Node *c) {
    if (a == tree->a && b == tree->b && c == tree->c) return (Node *)tree;
    Node *copy = node_new(tree->kind, a, b);
    copy->c = c;
    copy->value = tree->value;
    copy->name = tree->name;
    copy->op = tree->op;
    return copy;
}

/* Ritorna tree con ogni sotto-albero senza lettere che vale un numero
 * intero sostituito da quel numero: (3 - 1)! diventa 2, (-1)^{3 - 1}
 * diventa 1. Serve prima di calcolare con gli intervalli, che non conoscono
 * i fattoriali e leggono un esponente solo se è un numero scritto, e alla
 * regola delle potenze (27e), che deve sapere se un esponente è un intero.
 * I nodi che non cambiano restano gli stessi (node_rebuilt()). Mette 0 in
 * *closed, che chi chiama ha messo a 1, se tree contiene lettere. Un conto
 * che fallisce lascia l'albero com'è. */
Node *node_fold(const Node *tree, int *closed) {
    if (!tree) return NULL;
    if (tree->kind == N_NUM) return (Node *)tree;
    if (tree->kind == N_VAR || tree->kind == N_SEQ || tree->kind == N_BIGOP || tree->kind == N_APPLY || tree->kind == N_DERIV) { *closed = 0; return (Node *)tree; }
    int inside = 1;
    Node *a = node_fold(tree->a, &inside), *b = node_fold(tree->b, &inside);
    Node *copy = node_rebuilt(tree, a, b, tree->c);
    if (!inside) { *closed = 0; return copy; }

    /* Senza lettere: il valore, se è un intero. */
    const char *saved = failure;
    Scratch mark = scratch_mark();
    long long value;
    env_count = 0;
    int whole = rat_integer(eval(copy), &value) && failure == saved;
    failure = saved;
    scratch_drop(mark);
    return whole ? node_num(value) : copy;
}

/* Ritorna outer per la derivata di inner rispetto a x: la regola della
 * catena. Se inner è x stessa il fattore è 1 e non si scrive. */
Node *derive(const Node *f, int x);
static Node *chain(Node *outer, const Node *inner, int x) {
    if (inner->kind == N_VAR && inner->name == x) return outer;
    return node_new(N_MUL, outer, derive(inner, x));
}

/* Ritorna l'albero della derivata di f rispetto alla variabile x, con le
 * regole da 27c a 27g. Se f contiene qualcosa che non sa derivare fallisce,
 * e il valore ritornato non ha significato. La formula ha un valore solo
 * dove f è derivabile (vedi "Dove valgono le formule", in testa al
 * capitolo).
 *
 * Le semplificazioni sono solo quelle che evitano di scrivere zeri e
 * fattori 1: un fattore costante resta fuori dalla derivata, e la catena
 * tace la derivata di x. Il resto lo fa la valutazione. */
Node *derive(const Node *f, int x) {
    Node *u = f->a, *v = f->b;
    if (failure) return node_num(0);

    /* 27c. Costanti, la variabile, somme. */
    if (!node_has_variable(f, x)) return node_num(0);
    switch (f->kind) {
    case N_VAR: return node_num(1);
    case N_NEG: return node_new(N_NEG, derive(u, x), NULL);
    case N_ADD: case N_SUB:
        if (!node_has_variable(u, x)) return f->kind == N_ADD ? derive(v, x) : node_new(N_NEG, derive(v, x), NULL);
        if (!node_has_variable(v, x)) return derive(u, x);
        return node_new(f->kind, derive(u, x), derive(v, x));

    /* 27d. Prodotti e quozienti. */
    case N_MUL:
        if (!node_has_variable(u, x)) return node_new(N_MUL, u, derive(v, x));
        if (!node_has_variable(v, x)) return node_new(N_MUL, derive(u, x), v);
        return node_new(N_ADD, node_new(N_MUL, derive(u, x), v), node_new(N_MUL, u, derive(v, x)));
    case N_DIV:
        if (!node_has_variable(v, x)) return node_new(N_DIV, derive(u, x), v);
        if (!node_has_variable(u, x)) return node_new(N_NEG, node_new(N_DIV, node_new(N_MUL, u, derive(v, x)), node_new(N_POW, v, node_num(2))), NULL);
        return node_new(N_DIV, node_new(N_SUB, node_new(N_MUL, derive(u, x), v), node_new(N_MUL, u, derive(v, x))),
                        node_new(N_POW, v, node_num(2)));

    /* 27e. Potenze. Con la variabile solo nella base: c u^{c-1} u' se
     * l'esponente è un intero scritto come numero, altrimenti c u^c u' / u
     * (vedi la testa del capitolo). Con la variabile solo nell'esponente:
     * c^u ln(c) u'. Con la variabile in tutti e due: u^v = e^{v ln u}, la
     * regola della catena e quella del prodotto danno
     * u^v (v' ln u + v u' / u). */
    case N_POW: {
        /* L'esponente c - 1 si scrive già calcolato: gli intervalli (capitolo
         * 24), con cui la tabella dei segni ricontrolla le sue righe, leggono
         * come intero solo un esponente scritto come numero, e u^{3 - 1}
         * per loro non avrebbe valore dove u < 0. */
        int closed = 1;
        Node *whole = node_has_variable(v, x) ? NULL : node_fold(v, &closed);
        if (whole && whole->kind == N_NUM) return chain(node_new(N_MUL, whole, node_new(N_POW, u, node_num(whole->value - 1))), u, x);
        if (whole) return node_new(N_DIV, node_new(N_MUL, node_new(N_MUL, v, (Node *)f), derive(u, x)), u);
        if (!node_has_variable(u, x)) {
            if (u->kind == N_VAR && u->name == 'e') return chain((Node *)f, v, x);
            return chain(node_new(N_MUL, (Node *)f, node_call(FN_LN, u, NULL)), v, x);
        }
        return node_new(N_MUL, (Node *)f, node_new(N_ADD, node_new(N_MUL, derive(v, x), node_call(FN_LN, u, NULL)),
                                                  node_new(N_DIV, node_new(N_MUL, v, derive(u, x)), u)));
    }

    /* 27f. Funzioni: la regola della catena. */
    case N_CALL:
        switch ((Function)f->op) {
        case FN_SIN: return chain(node_call(FN_COS, u, NULL), u, x);
        case FN_COS: return chain(node_new(N_NEG, node_call(FN_SIN, u, NULL), NULL), u, x);
        case FN_TAN: return node_new(N_DIV, derive(u, x), node_new(N_POW, node_call(FN_COS, u, NULL), node_num(2)));
        case FN_COT: return node_new(N_NEG, node_new(N_DIV, derive(u, x), node_new(N_POW, node_call(FN_SIN, u, NULL), node_num(2))), NULL);
        case FN_LN:
            /* (ln|w|)' = w'/w dove w non è zero: dove w > 0 è (ln w)', dove
             * w < 0 è (ln(-w))' = -w'/(-w). È la regola che serve a
             * ricontrollare le primitive con ln|w|. */
            if (u->kind == N_CALL && u->op == FN_ABS) u = u->a;
            return node_new(N_DIV, derive(u, x), u);
        case FN_LOG:
            /* log_b u = ln u / ln b, dove b > 0 e b diverso da 1: con b
             * costante si divide per ln b (e con b = e non si divide), con x
             * nella base si deriva il quoziente. */
            if (!v) break;
            if (node_has_variable(v, x)) return derive(node_new(N_DIV, node_call(FN_LN, u, NULL), node_call(FN_LN, v, NULL)), x);
            if (v->kind == N_VAR && v->name == 'e') return derive(node_call(FN_LN, u, NULL), x);
            return node_new(N_DIV, derive(node_call(FN_LN, u, NULL), x), node_call(FN_LN, v, NULL));
        case FN_ARCTAN: return node_new(N_DIV, derive(u, x), node_new(N_ADD, node_num(1), node_new(N_POW, u, node_num(2))));
        case FN_ARCCOT: return node_new(N_NEG, node_new(N_DIV, derive(u, x), node_new(N_ADD, node_num(1), node_new(N_POW, u, node_num(2)))), NULL);
        case FN_ARCSIN: case FN_ARCCOS: {
            /* sin y = u con y in [-pi/2, pi/2] dà cos(y) y' = u', e lì
             * cos y = sqrt(1 - u^2); per l'arcocoseno, cos y = u con y in
             * [0, pi], -sin(y) y' = u' e sin y = sqrt(1 - u^2). */
            Node *slope = node_new(N_DIV, derive(u, x), node_call(FN_ROOT, node_new(N_SUB, node_num(1), node_new(N_POW, u, node_num(2))), node_num(2)));
            return f->op == FN_ARCSIN ? slope : node_new(N_NEG, slope, NULL);
        }
        case FN_ROOT:
            if (node_has_variable(v, x)) break;
            return node_new(N_DIV, node_new(N_MUL, (Node *)f, derive(u, x)), node_new(N_MUL, v, u));
        case FN_ABS:
            /* |u| vale u dove u > 0 e -u dove u < 0: la derivata è u' o -u',
             * cioè u' per il segno di u, che è u / |u|. */
            return node_new(N_DIV, node_new(N_MUL, derive(u, x), u), (Node *)f);
        default: break;
        }
        break;

    /* 27g. Una somma finita, con gli estremi che non dipendono da x. */
    case N_BIGOP: {
        if (f->op || f->name == x || node_has_variable(u, x) || node_has_variable(v, x)) break;
        Node *sum = node_new(N_BIGOP, u, v);
        sum->name = f->name;
        sum->c = derive(f->c, x);
        return sum;
    }
    default:
        break;
    }
    fail("derivata di un'espressione che le regole di derivazione del programma non trattano");
    return node_num(0);
}

/* I punti in cui le derivate vengono controllate con i numeri. Sono scelti
 * perché le funzioni degli esercizi vi siano definite: positivi e negativi,
 * uno minore di 1/2, e alcuni più lontani dall'origine, per le funzioni
 * definite solo oltre un numero (ln(x - 2), una radice di x + 2), che un
 * segno di derivata dentro un'espressione (27j) deve poter confermare. */
static const Frac derivative_points[] = {{3, 10}, {7, 5}, {-9, 10}, {13, 5}, {-11, 5}, {23, 4}};
enum { DERIVATIVE_POINTS = sizeof derivative_points / sizeof *derivative_points };

/* Ritorna una copia di tree pronta per essere calcolata con i numeri nella
 * sola variabile x: la lettera order vale l'intero at, ogni altra lettera
 * (tranne e, che è un numero) un razionale fisso, diverso da lettera a
 * lettera, e i sotto-alberi interi sono già calcolati (node_fold()). */
Node *sample_tree(const Node *tree, int x, int order, long long at) {
    Node *copy = node_replace(tree, order, node_num(at));
    for (int letter = 'A'; letter <= 'z'; letter++) {
        if (!isalpha(letter) || letter == x || letter == 'e' || !node_has_variable(copy, letter)) continue;
        copy = node_replace(copy, letter, node_new(N_DIV, node_num(3 + letter % 7), node_num(2 + letter % 5)));
    }
    return node_fold(copy, &(int){1});
}

/* LE DERIVATE CON I NUMERI: LA SERIE DI TAYLOR TRONCATA (27h)
 *
 * Il problema. Per controllare derive() serve la derivata di f in un punto
 * x0 calcolata senza le sue regole. Il rapporto incrementale
 * (f(x0 + h) - f(x0 - h)) / (2h) non va bene: sbaglia di circa h^2, e con h
 * piccolo perde cifre sottraendo due numeri quasi uguali. Dire "la derivata
 * delle regole è sbagliata" chiederebbe allora una tolleranza scelta a
 * occhio tra due double, cioè proprio un confronto in virgola mobile che
 * decide. Qui la derivata si calcola invece esatta, con i numeri.
 *
 * L'idea: i numeri duali. Si calcola f non su un numero ma su una coppia
 * a + a' eps, con la sola regola eps^2 = 0:
 *
 *     (a + a' eps) + (b + b' eps) = (a + b) + (a' + b') eps,
 *     (a + a' eps) (b + b' eps)   = a b + (a' b + a b') eps.
 *
 * La seconda componente segue da sé la regola della somma e quella del
 * prodotto. Partendo da x0 + 1 eps, alla fine del conto si ha
 * f(x0) + f'(x0) eps: la derivata esatta, senza errore di troncamento,
 * perché non si è approssimato nulla, si è solo portato un numero in più in
 * ogni conto. È la differenziazione automatica "in avanti".
 *
 * Con eps^{K+1} = 0 al posto di eps^2 = 0 la coppia diventa un polinomio in
 * eps di grado K: i primi termini della serie di Taylor di f in x0,
 *
 *     f(x0 + eps) = c_0 + c_1 eps + ... + c_K eps^K + (termini di grado > K),
 *     con c_k = f^(k)(x0) / k!,
 *
 * da cui si leggono tutte le derivate fino alla K-esima in un colpo solo.
 * Somma e prodotto sono quelli dei polinomi, buttando i gradi oltre K: un
 * termine buttato non contribuisce mai ai gradi più bassi, quindi c_0, ...,
 * c_K restano esatti. Per una funzione di u si usa l'equazione
 * differenziale che la funzione soddisfa, e confrontando i coefficienti di
 * eps^{k-1} se ne ricava una ricorrenza. Per e = exp(u), che ha e' = u' e:
 *
 *     k e_k = sum_{i=1..k} i u_i e_{k-i}.
 *
 * Le altre, con u = u_0 + u_1 eps + ...:
 *
 *   27h-1. q = a / b, da b q = a:  q_k = (a_k - sum_{i=1..k} b_i q_{k-i}) / b_0;
 *   27h-2. s = sin u e c = cos u, da s' = c u' e c' = -s u':
 *            k s_k = sum_{i=1..k} i u_i c_{k-i},  k c_k = -sum_{i=1..k} i u_i s_{k-i};
 *          tan u = s / c e cot u = c / s, con 27h-1;
 *   27h-3. y con y_0 dato e w y' = u':
 *            y_k = (k u_k - sum_{j=1..k-1} (k - j) w_j y_{k-j}) / (k w_0);
 *          è ln u con w = u, ed è arctan u con w = 1 + u^2; arccot u è
 *          pi/2 - arctan u. Per y = arcsin u, che ha sin y = u, è
 *          cos(y) y' = u': w = cos y dipende da y, ma per y_k servono solo
 *          w_0, ..., w_{k-1}, che le ricorrenze di 27h-2 danno da y_1, ...,
 *          y_{k-1}, già calcolati; così anche arccos u, con cos y = u e
 *          w = -sin y. La radice di 1 - u^2 della regola di derive() qui
 *          non compare;
 *   27h-4. u^v = exp(v ln u), per u_0 > 0; con v intero scritto come
 *          numero, prodotti ripetuti, per ogni u_0. La radice m-esima è
 *          exp(ln(u) / m), log_b u è ln u / ln b;
 *   27h-5. una somma \sum, o un prodotto \prod, con gli estremi numeri si
 *          svolge, termine per termine.
 *
 * (Riferimenti: A. Griewank, A. Walther, Evaluating Derivatives, SIAM 2008,
 * capitolo 13; R. E. Moore, Methods and Applications of Interval Analysis,
 * SIAM 1979, per le serie di Taylor con gli intervalli.)
 *
 * Perché ci si può credere. Il punto x0 è un intervallo minuscolo che lo
 * contiene, e ogni coefficiente è calcolato con le operazioni del capitolo
 * 24, ognuna delle quali dà un intervallo che contiene il risultato vero
 * per ogni scelta dei dati nei loro intervalli: quindi l'intervallo finale
 * contiene il vero c_k. E ogni operazione si fa solo dove la funzione è
 * analitica: se b_0 può essere zero, o se sotto un logaritmo u_0 può non
 * essere positivo, il coefficiente c_0 è "non so", e allora si dichiara
 * "non so" la serie intera (lì f non è derivabile, o non si sa). Questo
 * conta: le ricorrenze del logaritmo, per esempio, darebbero c_1 = u_1 / u_0
 * anche con u_0 < 0, dove ln u non esiste.
 *
 * Perché è indipendente da derive(). La serie si costruisce dall'albero
 * della funzione di partenza, non da quello delle derivate, e le regole
 * sono scritte qui una seconda volta in un'altra forma: la tangente come
 * quoziente di serie e non come 1 / cos^2, le radici e le potenze attraverso
 * exp e ln, il logaritmo e l'arcotangente con 27h-3. Un errore di derive()
 * non si ripete uguale qui. */

/* Ritorna la costante value come serie di ordine order. */
static Jet jet_constant(Range value, int order) {
    Jet jet = {order, {{0, 0}}};
    jet.c[0] = value;
    return jet;
}

/* Ritorna a + sign b, con sign uguale a 1 oppure a -1. */
static Jet jet_add(Jet a, Jet b, int sign) {
    for (int k = 0; k <= a.order; k++) a.c[k] = sign > 0 ? range_add(a.c[k], b.c[k]) : range_sub(a.c[k], b.c[k]);
    return a;
}

/* Ritorna a b: il prodotto dei due polinomi, senza i gradi oltre order. */
static Jet jet_mul(Jet a, Jet b) {
    Jet product = jet_constant((Range){0, 0}, a.order);
    for (int k = 0; k <= a.order; k++)
        for (int i = 0; i <= k; i++) product.c[k] = range_add(product.c[k], range_mul(a.c[i], b.c[k - i]));
    return product;
}

/* Ritorna a / b (27h-1). Quando si calcola q_k, i q_{k-i} sono già finiti. */
static Jet jet_div(Jet a, Jet b) {
    Jet q = a;
    for (int k = 0; k <= a.order; k++) {
        for (int i = 1; i <= k; i++) q.c[k] = range_sub(q.c[k], range_mul(b.c[i], q.c[k - i]));
        q.c[k] = range_div(q.c[k], b.c[0]);
    }
    return q;
}

/* Ritorna a elevato all'intero e, con prodotti ripetuti (27h-4). */
static Jet jet_power(Jet a, long long e) {
    Jet one = jet_constant((Range){1, 1}, a.order), power = one;
    for (long long i = 0; i < (e < 0 ? -e : e); i++) power = jet_mul(power, a);
    return e < 0 ? jet_div(one, power) : power;
}

/* Ritorna exp(u), con la ricorrenza della testa di questa parte. */
static Jet jet_exp(Jet u) {
    Jet e = jet_constant(range_exp(u.c[0]), u.order);
    for (int k = 1; k <= u.order; k++) {
        for (int i = 1; i <= k; i++) e.c[k] = range_add(e.c[k], range_mul(range_mul(range_ratio(i, 1), u.c[i]), e.c[k - i]));
        e.c[k] = range_div(e.c[k], range_ratio(k, 1));
    }
    return e;
}

/* Ritorna la serie y con y_0 = start e w y' = u' (27h-3). */
static Jet jet_solve(Range start, Jet u, Jet w) {
    Jet y = jet_constant(start, u.order);
    for (int k = 1; k <= u.order; k++) {
        Range sum = range_mul(range_ratio(k, 1), u.c[k]);
        for (int j = 1; j < k; j++) sum = range_sub(sum, range_mul(range_mul(range_ratio(k - j, 1), w.c[j]), y.c[k - j]));
        y.c[k] = range_div(sum, range_mul(range_ratio(k, 1), w.c[0]));
    }
    return y;
}

/* Ritorna ln u: 27h-3 con w = u. */
static Jet jet_ln(Jet u) { return jet_solve(range_ln(u.c[0]), u, u); }

/* Ritorna arctan u: 27h-3 con w = 1 + u^2. */
static Jet jet_atan(Jet u) { return jet_solve(range_atan(u.c[0]), u, jet_add(jet_constant((Range){1, 1}, u.order), jet_mul(u, u), 1)); }

/* Mette in *sine e *cosine sin u e cos u (27h-2). Le due ricorrenze si
 * intrecciano: s_k usa i c_j con j < k, e viceversa, già finiti. */
static void jet_sin_cos(Jet u, Jet *sine, Jet *cosine) {
    Jet s = jet_constant(range_none(), u.order), c = s;
    range_sin_cos(u.c[0], &s.c[0], &c.c[0]);
    for (int k = 1; k <= u.order; k++) {
        for (int i = 1; i <= k; i++) {
            Range step = range_mul(range_ratio(i, 1), u.c[i]);
            s.c[k] = range_add(s.c[k], range_mul(step, c.c[k - i]));
            c.c[k] = range_sub(c.c[k], range_mul(step, s.c[k - i]));
        }
        s.c[k] = range_div(s.c[k], range_ratio(k, 1));
        c.c[k] = range_div(c.c[k], range_ratio(k, 1));
    }
    *sine = s;
    *cosine = c;
}

/* Ritorna arcsin u (sine = 1) o arccos u (sine = 0), con 27h-3: y_k viene
 * da w y' = u', con w = cos y per l'arcoseno e w = -sin y per l'arcocoseno,
 * e insieme a y si costruiscono, un grado alla volta, le serie di sin y e
 * cos y (27h-2). Il valore y_0 lo dà range_asin(). Dove |u_0| non è di
 * sicuro minore di 1, w_0 può essere zero e la divisione dà "non so": lì la
 * funzione non è derivabile, o non si sa. */
static Jet jet_arc(Jet u, int sine) {
    Range start = sine ? range_asin(u.c[0]) : range_from_half_pi(range_asin(u.c[0]));
    Jet y = jet_constant(start, u.order), s = y, c = y;
    range_sin_cos(start, &s.c[0], &c.c[0]);
    for (int k = 1; k <= u.order; k++) {
        /* y_k, con i w_j per j < k già noti. */
        Range sum = range_mul(range_ratio(k, 1), u.c[k]);
        for (int j = 1; j < k; j++) sum = range_sub(sum, range_mul(range_mul(range_ratio(k - j, 1), sine ? c.c[j] : range_neg(s.c[j])), y.c[k - j]));
        y.c[k] = range_div(sum, range_mul(range_ratio(k, 1), sine ? c.c[0] : range_neg(s.c[0])));

        /* s_k e c_k, che chiedono y_1, ..., y_k. */
        s.c[k] = c.c[k] = (Range){0, 0};
        for (int i = 1; i <= k; i++) {
            Range step = range_mul(range_ratio(i, 1), y.c[i]);
            s.c[k] = range_add(s.c[k], range_mul(step, c.c[k - i]));
            c.c[k] = range_sub(c.c[k], range_mul(step, s.c[k - i]));
        }
        s.c[k] = range_div(s.c[k], range_ratio(k, 1));
        c.c[k] = range_div(c.c[k], range_ratio(k, 1));
    }
    return y;
}

/* Ritorna la serie di Taylor di ordine order, nel punto at, dell'espressione
 * node, già passata da sample_tree(): x è la variabile, e le sole altre
 * lettere ammesse sono e e pi greco. La serie è "non so" dove il calcolo non
 * riesce, o dove node non è definita o non è derivabile; anche per ciò che
 * qui non si calcola (un fattoriale di x, un'applicazione). Con order = 0 è
 * il valore di node in at.
 *
 * Sfrutta node_fold() e node_replace() per svolgere somme e prodotti: i nodi
 * che crea per un termine li toglie dall'arena appena calcolato il termine. */
Jet jet_eval(const Node *node, int x, Range at, int order) {
    Jet a, sine, cosine, result = jet_constant(range_none(), order);
    switch (node->kind) {
    case N_NUM: result = jet_constant(range_ratio(node->value, 1), order); break;
    case N_VAR:
        /* x è x0 + eps; la lettera e è il numero di Nepero. */
        if (node->name == x) {
            result = jet_constant(at, order);
            if (order > 0) result.c[1] = (Range){1, 1};
        } else if (node->name == VAR_PI) result = jet_constant(range_pi(), order);
        else if (node->name == 'e') result = jet_constant(range_exp_at(1), order);
        break;
    case N_NEG: result = jet_add(jet_constant((Range){0, 0}, order), jet_eval(node->a, x, at, order), -1); break;
    case N_ADD: case N_SUB:
        result = jet_add(jet_eval(node->a, x, at, order), jet_eval(node->b, x, at, order), node->kind == N_ADD ? 1 : -1);
        break;
    case N_MUL: result = jet_mul(jet_eval(node->a, x, at, order), jet_eval(node->b, x, at, order)); break;
    case N_DIV: result = jet_div(jet_eval(node->a, x, at, order), jet_eval(node->b, x, at, order)); break;
    case N_POW: {
        /* 27h-4. L'esponente intero, scritto come numero (dopo node_fold()
         * anche negativo), con i prodotti; ogni altro con exp(v ln u). Il
         * limite sull'esponente è quello di node_range(). */
        const Node *exponent = node->b->kind == N_NEG ? node->b->a : node->b;
        long long e = exponent->kind != N_NUM ? MAX_UNI + 1 : node->b->kind == N_NEG ? -exponent->value : exponent->value;
        a = jet_eval(node->a, x, at, order);
        result = e >= -MAX_UNI && e <= MAX_UNI ? jet_power(a, e) : jet_exp(jet_mul(jet_eval(node->b, x, at, order), jet_ln(a)));
        break;
    }
    case N_CALL:
        a = jet_eval(node->a, x, at, order);
        switch (node->op) {
        case FN_SIN: case FN_COS: case FN_TAN: case FN_COT:
            jet_sin_cos(a, &sine, &cosine);
            if (node->op == FN_SIN || node->op == FN_COS) result = node->op == FN_SIN ? sine : cosine;
            else result = node->op == FN_TAN ? jet_div(sine, cosine) : jet_div(cosine, sine);
            break;
        case FN_LN: result = jet_ln(a); break;
        case FN_LOG:
            if (node->b) result = jet_div(jet_ln(a), jet_ln(jet_eval(node->b, x, at, order)));
            break;
        case FN_ARCTAN: result = jet_atan(a); break;
        case FN_ARCCOT: result = jet_add(jet_constant(range_from_half_pi((Range){0, 0}), order), jet_atan(a), -1); break;
        case FN_ARCSIN: case FN_ARCCOS: result = jet_arc(a, node->op == FN_ARCSIN); break;
        case FN_ROOT: {
            /* La radice m-esima è exp(ln(u) / m); con m dispari e u_0 < 0 è
             * la radice reale, -exp(ln(-u) / m) (11o). */
            int side, negative = node->b->kind == N_NUM && node->b->value % 2 && range_side(a.c[0], &side) && side < 0;
            Jet zero = jet_constant((Range){0, 0}, order), inside = negative ? jet_add(zero, a, -1) : a;
            if (node->b->kind == N_NUM && node->b->value >= 2) result = jet_exp(jet_div(jet_ln(inside), jet_constant(range_ratio(node->b->value, 1), order)));
            if (negative) result = jet_add(zero, result, -1);
            break;
        }
        case FN_ABS: {
            /* |u| è u oppure -u dove il segno di u è certo, e lì è derivabile. */
            int side;
            if (range_side(a.c[0], &side)) result = side > 0 ? a : jet_add(jet_constant((Range){0, 0}, order), a, -1);
            break;
        }
        default: break;
        }
        break;
    case N_BIGOP: {
        /* 27h-5. Una somma, o un prodotto, con gli estremi che, calcolati,
         * sono numeri. Come in 11a, l'estremo superiore può essere
         * l'inferiore meno 1, la somma (o il prodotto) vuota, ma non più
         * piccolo. */
        int closed = 1;
        const Node *low = node_fold(node->a, &closed), *high = node_fold(node->b, &closed);
        if (low->kind != N_NUM || high->kind != N_NUM) break;
        __int128 terms = (__int128)high->value - low->value + 1;
        if (terms < 0 || terms > MAX_UNROLL) break;
        result = jet_constant((Range){node->op ? 1 : 0, node->op ? 1 : 0}, order);
        for (long long i = 0; i < (long long)terms && !failure; i++) {
            Scratch mark = scratch_mark();
            Jet term = jet_eval(node_fold(node_replace(node->c, node->name, node_num(low->value + i)), &closed), x, at, order);
            result = node->op ? jet_mul(result, term) : jet_add(result, term, 1);
            scratch_drop(mark);
        }
        break;
    }
    default: break;
    }

    /* L'invariante: senza il valore, nessun coefficiente vale (vedi "Perché
     * ci si può credere"). Un'arena esaurita lascia alberi di riserva, che non
     * dicono nulla. */
    if (!range_known(result.c[0]) || failure)
        for (int k = 0; k <= order; k++) result.c[k] = range_none();
    return result;
}

/* Ritorna un intervallo che contiene il valore di tree, già passato da
 * sample_tree(), in at; "non so" se non si calcola o non è definito. */
Range sample_value(const Node *tree, int x, Range at) { return jet_eval(tree, x, at, 0).c[0]; }

/* Quanto devono essere vicini due valori dello stesso numero, calcolati in
 * due modi, per dire che coincidono: in rapporto alla grandezza del numero,
 * più 1. È molto più largo dell'errore degli intervalli, e molto più stretto
 * dello scarto che dà una regola sbagliata. */
#define AGREEMENT 1e-9

/* Confronta due intervalli a e b che dovrebbero contenere lo stesso numero.
 * Ritorna -1 se i due numeri sono di sicuro diversi (gli intervalli non si
 * toccano); 1 se la loro distanza è di sicuro al più AGREEMENT (1 + |a|);
 * 0 se non si sa dire né l'una né l'altra cosa: un "non so", o intervalli
 * troppo larghi.
 *
 * Perché non è un confronto tra double che decide: la differenza vera sta
 * di sicuro in gap, quindi gap dentro [-room, room] è una disuguaglianza
 * garantita sulla differenza vera, ricavata da un intervallo come al
 * capitolo 24. E la risposta 1 non dimostra nulla: dice solo che il
 * controllo non ha trovato errori. */
int numbers_agree(Range a, Range b) {
    Range gap = range_sub(a, b);
    int side;
    if (range_side(gap, &side)) return -1;
    if (!range_known(gap)) return 0;
    double size = a.high > -a.low ? a.high : -a.low, room = AGREEMENT * (1 + size);
    return gap.low >= -room && gap.high <= room;
}

/* Il confronto, punto per punto, tra le derivate calcolate con le regole e
 * quelle lette dalla serie di Taylor (27h), per le derivate di ordine da 0
 * a order di una funzione. */
typedef struct {
    Range taylor[MAX_JET + 1][DERIVATIVE_POINTS];  /* [k][p]: la derivata k-esima vera in x_p */
    Range rules[MAX_JET + 1][DERIVATIVE_POINTS];   /* [k][p]: la derivata k-esima delle regole, calcolata in x_p */
    int agree[MAX_JET + 1];  /* [k]: il bit p è acceso se in x_p le due coincidono (numbers_agree() = 1) */
    int wrong;               /* 1 se, per qualche k e qualche p, sono di sicuro diverse */
} DerivativeCheck;

/* Riempie *check per una funzione, derived[0], e le sue derivate derived[1],
 * ..., derived[order] calcolate con le regole: tutti gli alberi sono già
 * passati da sample_tree(). In ogni punto di prova la serie di Taylor della
 * funzione si calcola una volta sola, fino all'ordine order, e la derivata
 * k-esima è k! per il coefficiente c_k. Per k = 0 il confronto è tra due
 * calcoli del valore della funzione: non controlla una regola, ma lo
 * stesso un FALSO con n = 0 vi si appoggia (27i). */
static void derivatives_check(DerivativeCheck *check, Node *const *derived, int order, int x) {
    memset(check, 0, sizeof *check);
    for (int p = 0; p < DERIVATIVE_POINTS; p++) {
        Range at = range_ratio(derivative_points[p].num, derivative_points[p].den), factorial = {1, 1};
        Jet taylor = jet_eval(derived[0], x, at, order);
        for (int k = 0; k <= order; k++) {
            if (k > 0) factorial = range_mul(factorial, range_ratio(k, 1));
            check->taylor[k][p] = range_mul(factorial, taylor.c[k]);
            check->rules[k][p] = sample_value(derived[k], x, at);
            int agreement = numbers_agree(check->rules[k][p], check->taylor[k][p]);
            if (agreement < 0) check->wrong = 1;
            if (agreement > 0) check->agree[k] |= 1 << p;
        }
    }
}

/* Ritorna il numero di nodi di tree, contando una volta per ogni strada i
 * sotto-alberi condivisi: è il costo di un conto sull'albero. */
long long node_count(const Node *tree) {
    return tree ? 1 + node_count(tree->a) + node_count(tree->b) + node_count(tree->c) : 0;
}

/* Riempie direct[1], ..., direct[order] con le derivate di direct[0]
 * rispetto a x, con le regole, e *check con il loro confronto con la serie
 * di Taylor (27h). Ritorna 1 se nessuna è smentita in nessun punto e
 * ognuna coincide con la serie in almeno un punto. Altrimenti il motivo è
 * in `failure`, e ritorna 0 se le regole non si applicano (la funzione
 * contiene qualcosa che non sanno derivare, o la derivata è troppo lunga),
 * -1 se la derivata non è confermata. Una smentita, che è l'errore di una
 * regola, conta tra i passi scartati. */
static int derivatives_confirmed(Node **direct, int order, int x, DerivativeCheck *check) {
    Node *sampled[MAX_JET + 1];
    for (int k = 1; k <= order && !failure; k++) {
        direct[k] = derive(direct[k - 1], x);
        if (!failure && node_count(direct[k]) > MAX_DERIVATIVE_NODES) fail("la derivata calcolata con le regole è troppo lunga");
    }
    for (int k = 0; k <= order && !failure; k++) sampled[k] = sample_tree(direct[k], x, 0, 0);
    if (failure) return 0;
    derivatives_check(check, sampled, order, x);
    if (failure) return -1;
    if (check->wrong) {
        unjustified_steps++;
        fail("una derivata calcolata con le regole di derivazione è smentita dalla serie di Taylor della funzione");
        return -1;
    }
    for (int k = 1; k <= order; k++)
        if (!check->agree[k]) { fail("non riesco a confermare con i numeri una derivata calcolata con le regole di derivazione: nei punti di prova la funzione non è definita, o i numeri non bastano"); return -1; }
    return 1;
}

/* Ritorna 1 se tree è un nodo che node_domain() sostituisce: un arcoseno,
 * un arcocoseno, il logaritmo di un valore assoluto. */
static int node_special(const Node *tree) {
    if (tree->kind != N_CALL) return 0;
    if (tree->op == FN_ARCSIN || tree->op == FN_ARCCOS) return 1;
    return (tree->op == FN_LN || tree->op == FN_LOG) && tree->a->kind == N_CALL && tree->a->op == FN_ABS;
}

/* Ritorna 1 se in tree compare un nodo che node_domain() sostituisce. */
static int node_has_special(const Node *tree) {
    return tree && (node_special(tree) || node_has_special(tree->a) || node_has_special(tree->b) || node_has_special(tree->c));
}

/* Ritorna un'espressione che ha un valore esattamente dove lo ha f, fatta di
 * ciò che la valutazione e la tabella dei segni sanno calcolare: f stessa,
 * con ogni arcoseno e arcocoseno di u sostituito da u + 0 sqrt(1 - u^2), che
 * come loro è definito dove u lo è e |u| <= 1, e ogni ln|u| (log_b |u|) da
 * 1 / u (1 / (u ln b)), definito come lui dove u non è zero (e b > 0 e
 * diverso da 1). Il valore è un altro: conta solo dove c'è. Un nodo così
 * dentro l'argomento di un altro resta com'è, perché lì servirebbe proprio
 * il suo valore, e la valutazione lo rifiuterà. */
static Node *node_domain(const Node *f) {
    if (!f || !node_has_special(f)) return (Node *)f;
    if (node_special(f) && f->op == FN_LN && !node_has_special(f->a->a)) return node_new(N_DIV, node_num(1), f->a->a);
    if (node_special(f) && f->op == FN_LOG && !node_has_special(f->a->a) && !node_has_special(f->b))
        return node_new(N_DIV, node_num(1), node_new(N_MUL, f->a->a, node_call(FN_LN, f->b, NULL)));
    if (node_special(f) && f->op != FN_LN && f->op != FN_LOG && !node_has_special(f->a)) {
        Node *radicand = node_new(N_SUB, node_num(1), node_new(N_POW, f->a, node_num(2)));
        return node_new(N_ADD, f->a, node_new(N_MUL, node_num(0), node_call(FN_ROOT, radicand, node_num(2))));
    }
    return node_rebuilt(f, node_domain(f->a), node_domain(f->b), node_domain(f->c));
}

/* 27j. IL SEGNO DI DERIVATA DENTRO UN'ESPRESSIONE
 *
 * A che cosa serve. Lo studio di una funzione si scrive con la sua
 * derivata: f cresce dove f' > 0, è convessa dove f'' > 0. Così
 *
 *     \{x \in \mathbb{R} \mid \frac{d}{dx}\left( x e^{x} \right) > 0\}
 *
 * chiede dove x e^x cresce, e la risposta la dà la tabella dei segni (18p),
 * con il suo metodo e i suoi controlli, se al posto del segno di derivata
 * c'è la derivata. Il lettore fa del segno un nodo N_DERIV (9d); qui, subito
 * dopo il parsing e prima di ogni conto, ogni nodo così diventa la sua
 * derivata. Chi non ci riesce lascia l'errore, e l'enunciato è NON
 * SUPPORTATO: un segno di derivata non si legge mai come altro.
 *
 * Che cosa prende il posto del segno. Siano d_1, ..., d_k le derivate di g
 * date dalle regole (27c-27g), e G un'espressione definita dove g lo è
 * (node_domain(): g stessa, salvo arcoseni, arcocoseni e ln|u|, che la
 * valutazione o la tabella dei segni non sanno calcolare). Il segno
 * \frac{d^k}{dx^k}(g) diventa
 *
 *     d_k + 0 (G + d_1 + ... + d_{k-1}).
 *
 * Vale d_k, ma ha un valore solo nell'insieme E dei punti in cui g, d_1,
 * ..., d_k ce l'hanno tutte: la valutazione annota le condizioni di
 * esistenza (denominatori, radicandi, argomenti dei logaritmi) di ogni
 * pezzo, anche di quello moltiplicato per zero, e gli intervalli lì non
 * danno un valore. È così che un punto in cui g non è definita non entra
 * nella risposta anche se d_k vi ha un valore: in \{x \mid (\ln x)' < 0\} la
 * derivata 1/x è negativa per x < 0, ma lì ln x non c'è, e la risposta è
 * vuota.
 *
 * Perché in E la derivata k-esima esiste e vale d_k. Per k = 1: ogni regola
 * dà una formula che ha un valore solo dove la funzione che deriva è
 * derivabile (vedi "Dove valgono le formule", in testa al capitolo), e lì
 * vale la sua derivata, per la regola della catena e quelle del prodotto e
 * del quoziente. Inoltre E è aperto: le condizioni di g che non sono strette
 * (un radicando non negativo, |u| <= 1 sotto un arcoseno) in d_1 diventano
 * strette, perché la derivata divide per il radicando, o per sqrt(1 - u^2).
 * Allora intorno a ogni punto di E la derivata prima esiste ed è d_1, e la
 * derivata di d_1 in quel punto è la seconda: lo stesso ragionamento, ordine
 * dopo ordine.
 *
 * Che cosa resta da controllare. Il contrario non vale: in un punto fuori
 * da E, dove però g è definita, la derivata può esistere. x|x| ha derivata
 * 2|x|, anche in 0, ma la regola del valore assoluto dà x^2/|x| + |x|, che in
 * 0 non ha valore. Lì l'espansione non dice nulla, e la tabella dei segni,
 * che conta come falso un confronto senza valore, direbbe il falso: se ne
 * occupa 27l.
 *
 * Il controllo indipendente. Le derivate d_1, ..., d_k di ogni segno vengono
 * confrontate con la serie di Taylor di g nei punti di prova, come in 27h
 * (derivatives_confirmed()): una smentita è un errore del programma, e ogni
 * ordine deve essere confermato in almeno un punto.
 */

/* Le espansioni dell'enunciato in corso, per il controllo di 27l: per ogni
 * segno, l'espressione definita dove lo è la funzione (G) e ciò che ha
 * preso il posto del segno. Valgono finché l'arena non viene svuotata. */
#define MAX_EXPANDED 8
static _Thread_local const Node *expanded_function[MAX_EXPANDED], *expanded_value[MAX_EXPANDED];

/* Vedi la dichiarazione in testa a questo file. I segni annidati,
 * \frac{d}{dx}(\frac{d}{dx}(g)), si espandono dal più interno: la funzione
 * del più esterno è già un'espansione, con le sue condizioni. */
Node *derivatives_expanded(Node *tree) {
    if (!tree || failure) return tree;
    Node *a = derivatives_expanded(tree->a), *b = derivatives_expanded(tree->b), *c = derivatives_expanded(tree->c);
    if (failure || tree->kind != N_DERIV) return failure ? tree : node_rebuilt(tree, a, b, c);
    int x = tree->name, order = (int)tree->value;
    if (order > MAX_DERIVATIVE_BASE) { fail("l'ordine di una derivata dentro un'espressione deve essere al più 4"); return tree; }
    if (derivative_signs == MAX_EXPANDED) { fail("troppi segni di derivata in un enunciato"); return tree; }

    /* Le derivate, confermate con i numeri (27h). */
    Node *direct[MAX_JET + 1] = {a};
    DerivativeCheck check;
    if (derivatives_confirmed(direct, order, x, &check) < 1) return tree;

    /* La derivata, con le condizioni di esistenza della funzione e delle
     * derivate prima di lei. */
    Node *domain = node_domain(a), *guard = domain;
    int closed = 1;
    for (int k = 1; k < order; k++) guard = node_new(N_ADD, guard, direct[k]);
    Node *value = node_fold(node_new(N_ADD, direct[order], node_new(N_MUL, node_num(0), guard)), &closed);
    expanded_function[derivative_signs] = domain;
    expanded_value[derivative_signs++] = value;
    return value;
}

/* Vedi la dichiarazione in testa a questo file. */
void formula_derivatives_expanded(Formula *f) {
    if (!f || failure) return;
    f->left = derivatives_expanded(f->left);
    f->right = derivatives_expanded(f->right);
    formula_derivatives_expanded(f->a);
    formula_derivatives_expanded(f->b);
}

/* Ritorna tree con le scritture del numero e che la valutazione non
 * riconosce sostituite dal loro valore: ln e = 1, log_b e = 1 / ln b,
 * log_e u = ln u. Sono identità dove i due membri sono definiti (b > 0 e
 * diverso da 1, u > 0), e in questo capitolo la lettera e è il numero di
 * Nepero; la valutazione, che serve anche agli enunciati in cui e è una
 * lettera qualsiasi, non le applica da sé. I libri scrivono così le
 * derivate dei logaritmi: (\log_{\frac{2}{3}} x)' = \frac{\log_{\frac{2}{3}} e}{x}. */
static Node *node_euler(const Node *tree) {
    if (!tree) return NULL;
    Node *a = node_euler(tree->a), *b = node_euler(tree->b);
    int euler_a = a && a->kind == N_VAR && a->name == 'e', euler_b = b && b->kind == N_VAR && b->name == 'e';
    if (tree->kind == N_CALL && tree->op == FN_LN && euler_a) return node_num(1);
    if (tree->kind == N_CALL && tree->op == FN_LOG && euler_b) return node_call(FN_LN, a, NULL);
    if (tree->kind == N_CALL && tree->op == FN_LOG && euler_a) return node_new(N_DIV, node_num(1), node_call(FN_LN, b, NULL));
    return node_rebuilt(tree, a, b, node_euler(tree->c));
}

/* 27a, il conto. Ritorna 1 se left - right si riduce a zero con l'algebra
 * esatta, con la lettera order (0 se non c'è) uguale a base, dove i due
 * membri sono definiti; x è la variabile, che se è la lettera e non è il
 * numero di Nepero. left è una derivata della funzione function, che non
 * entra nel conto ma ne dà i fatti del dominio (12d): dove la derivata
 * esiste, la funzione è definita.
 *
 * I valori assoluti. La valutazione non sa calcolare |u| di
 * un'espressione: |u| vale u dove u >= 0 e -u dove u <= 0. Si fa allora il
 * conto per ogni scelta dei segni (u oppure -u per ogni valore assoluto),
 * con lo stesso meccanismo della tabella dei segni (abs_pattern), e si
 * chiede che la differenza si riduca a zero in ognuna. Basta: in ogni punto
 * x ogni |u| vale u(x) oppure -u(x), quindi la differenza in x è quella di
 * una delle scelte, che è zero. Due valori assoluti scritti allo stesso modo
 * sono uno solo (abs_collect()); con argomenti diversi si provano tutte le
 * combinazioni, anche quelle che in nessun punto si verificano: si dimostra
 * qualcosa in meno, mai di più. Dentro una scelta il conto riguarda solo i
 * punti in cui ogni u ha il segno scelto, e quel segno è un fatto (11q): con
 * \cos x >= 0, \sqrt{1 - \sin^2 x} = \cos x.
 *
 * Il dominio. Il test è quello dove i due membri sono definiti (12d): i
 * radicandi delle radici di indice pari e gli argomenti dei logaritmi sono
 * fatti, e \sqrt[3]{x} accanto a \sqrt{x} è x^{1/3} come (\sqrt[6]{x})^2. Si
 * può perché la derivata si afferma solo lì, e che lì ci sia almeno un punto
 * lo dicono i controlli con i numeri, che chi chiama ha già fatto.
 *
 * Le potenze che la valutazione non sa calcolare. e^{\sin x} non ha una
 * forma esatta: il seno è scritto con gli esponenziali complessi, e
 * l'esponente risulta complesso. Ma se la stessa potenza T, con x
 * all'esponente, compare in tutti e due i membri, al suo posto si può
 * mettere una lettera nuova t: se la differenza si riduce a zero per ogni
 * valore di t, si riduce a zero anche per t = T(x). Si dimostra di più di
 * quanto serve, quindi niente di falso. Lo si fa solo con le potenze che
 * il conto non sa fare: delle altre si perderebbero le relazioni con il
 * resto, come e^{2x} = (e^{x})^2. */
static Node *node_swapped(const Node *tree, const Node *pattern, int letter) {
    if (!tree) return NULL;
    if (node_equal(tree, pattern)) {
        Node *variable = node_new(N_VAR, NULL, NULL);
        variable->name = letter;
        return variable;
    }
    return node_rebuilt(tree, node_swapped(tree->a, pattern, letter), node_swapped(tree->b, pattern, letter), node_swapped(tree->c, pattern, letter));
}

/* Ritorna 1 se in tree compare un sotto-albero scritto come pattern. */
static int node_occurs(const Node *tree, const Node *pattern) {
    return tree && (node_equal(tree, pattern) || node_occurs(tree->a, pattern) || node_occurs(tree->b, pattern) || node_occurs(tree->c, pattern));
}

/* Ritorna una potenza con x all'esponente che compare in tree e in other, e
 * che la valutazione non sa calcolare; NULL se non ce n'è. */
static const Node *shared_power(const Node *tree, const Node *other, int x) {
    if (!tree) return NULL;
    if (tree->kind == N_POW && node_has_variable(tree->b, x) && node_occurs(other, tree)) {
        const char *was = failure;
        Scratch mark = scratch_mark();
        failure = NULL;
        eval(tree);
        int unknown = failure != NULL;
        failure = was;
        scratch_drop(mark);
        if (unknown) return tree;
    }
    const Node *found = shared_power(tree->a, other, x);
    if (!found) found = shared_power(tree->b, other, x);
    return found ? found : shared_power(tree->c, other, x);
}

int derivative_identity(const Node *left, const Node *right, const Node *function, int order, long long base, int x) {
    Statement s = {(Node *)left, (Node *)right, REL_EQ};
    const Node *source = function;
    int holds = 1, kept = induction_var;
    if (x != 'e') { s.lhs = node_euler(left); s.rhs = node_euler(right); source = node_euler(function); }

    /* Le potenze in comune che il conto non sa fare, una lettera nuova
     * per ognuna: le lettere maiuscole, che qui non nominano nulla. La
     * funzione, che dà solo i fatti del dominio, cambia allo stesso modo, e
     * nemmeno lei deve usare la lettera: due quantità diverse con lo stesso
     * nome darebbero un fatto falso. */
    for (int letter = 'A', tries = 0; letter <= 'Z' && tries < 4; letter++) {
        if (node_uses_letter(s.lhs, letter) || node_uses_letter(s.rhs, letter) || node_uses_letter(source, letter)) continue;
        const Node *power = shared_power(s.lhs, s.rhs, x);
        if (!power) break;
        s.lhs = node_swapped(s.lhs, power, letter);
        s.rhs = node_swapped(s.rhs, power, letter);
        source = node_swapped(source, power, letter);
        tries++;
    }
    abs_count = 0;
    abs_collect(s.lhs);
    abs_collect(s.rhs);
    int count = abs_count, points = point_count;
    induction_var = order;

    /* Nessun parametro con un valore (13e): l'identità deve valere per ogni
     * valore delle altre lettere, non per quelli di un conto precedente. Il
     * test di annullamento è quello dove i due membri sono definiti (12d):
     * l'uguaglianza si afferma solo lì, e in ogni caso dei valori assoluti
     * il segno scelto per ognuno è un fatto (11q). */
    point_count = 0;
    for (abs_pattern = 0; holds && !failure && abs_pattern < 1u << count; abs_pattern++) {
        abs_count = count;
        holds = vanishes_where_defined(&s, source, rat_int(base));
    }
    abs_count = 0;
    abs_pattern = 0;
    induction_var = kept;
    point_count = points;
    return holds && !failure;
}

/* 27a, la rilettura con i numeri. Ritorna 1 se le formule scritte nei pezzi
 * a e b della dimostrazione, rilette dal testo con il lettore del programma,
 * hanno lo stesso valore, con gli intervalli (27h), in almeno uno dei punti
 * di prova, e non sono di sicuro diverse in nessuno. È la rilettura di
 * riserva per ciò che 13g non sa calcolare con i numeri esatti: e^{\sin x}
 * in un punto razionale non è un numero che il conto esatto sappia
 * scrivere. Come in 13g, chi scrive e chi rilegge non hanno nulla in
 * comune: la scrittura parte dagli alberi, il controllo dai caratteri. */
static int reread_numbers(Span a, Span b, int x) {
    char text[2][MAX_FORMULA];
    Node *tree[2];
    size_t kept = arena_used;
    int agreed = 0, sound = 1;
    for (int i = 0; i < 2 && sound; i++) {
        Span piece = i ? b : a;
        size_t length = piece.to - piece.from;
        sound = length < MAX_FORMULA;
        if (!sound) break;
        memcpy(text[i], proof_text + piece.from, length);
        text[i][length] = '\0';
        tree[i] = parse_expression(text[i]);
        sound = !syntax_error && !failure;
        if (sound) tree[i] = sample_tree(tree[i], x, 0, 0);
    }
    for (int p = 0; p < DERIVATIVE_POINTS && sound && !failure; p++) {
        Range at = range_ratio(derivative_points[p].num, derivative_points[p].den);
        int agreement = numbers_agree(sample_value(tree[0], x, at), sample_value(tree[1], x, at));
        if (agreement < 0) sound = 0;
        agreed += agreement > 0;
    }
    sound = sound && !failure && agreed > 0;
    syntax_error = failure = NULL;
    arena_used = kept;
    return sound;
}

/* Ritorna 1 se in tree compare una potenza con x sia nella base sia
 * nell'esponente: il verdetto deve dire che la si intende e^{v ln u}. */
static int node_has_tower(const Node *tree, int x) {
    if (!tree) return 0;
    if (tree->kind == N_POW && node_has_variable(tree->a, x) && node_has_variable(tree->b, x)) return 1;
    return node_has_tower(tree->a, x) || node_has_tower(tree->b, x) || node_has_tower(tree->c, x);
}

/* 27m. IL CERTIFICATO DI UNA DERIVATA (E DI UNA PRIMITIVA)
 *
 * A che cosa serve. Le regole di derivazione sono scritte una volta sola, in
 * derive(), e i controlli di 27h e 27i sono con i numeri, in pochi punti. Il
 * certificato porta a checker.c (capitolo 13) la funzione e la derivata
 * affermata, e il verificatore deriva da sé, con regole sue, e decide con la
 * sua algebra esatta se la differenza è zero. Lo stesso per una primitiva
 * (la sua derivata deve essere la funzione integranda) e per un integrale
 * definito (capitolo 30, 30cert). Sta qui, prima di 27k, perché 27k e
 * prove_derivative() lo usano.
 *
 * Che cosa si scrive. Il tipo, la variabile, l'ordine ("order 2", oppure
 * "order n base 1" per una derivata n-esima), le espressioni come sono negli
 * alberi dell'enunciato (o della risposta riletta dal testo, per una
 * richiesta), con le parole di cert_real; per un integrale anche gli estremi
 * e il valore. Poi, come suggerimenti, i fattori in cui il motore ha
 * scomposto gli argomenti dei logaritmi (le basi degli atomi LN dell'ultimo
 * conto), quelli che la notazione sa scrivere: un suggerimento sbagliato non
 * divide nulla e non ha effetto.
 *
 * Che cosa non si scrive: arcoseno e arcocoseno e le successioni del
 * vocabolario. Allora il certificato manca, e il verdetto dice perché.
 *
 * Le risposte. Accettato: il verdetto porta il certificato, che dimostra il
 * teorema in testa al capitolo 13 di checker.c: la derivata vale dove la
 * funzione è regolare (definita, con i radicandi e gli argomenti dei valori
 * assoluti diversi da zero) e la formula è definita. Se la funzione ha radici, potenze con un esponente
 * non intero o valori assoluti, il verdetto lo dice in una nota: nei punti in
 * cui un radicando, o l'argomento di un valore assoluto, vale zero il
 * certificato non dice nulla. Respinto: il motore e il
 * verificatore non sono d'accordo, quindi nel dubbio non è dimostrato, e il
 * passo conta tra quelli che non hanno superato il controllo. Non
 * controllabile: il verdetto resta, e dice perché il certificato manca. */

/* Ritorna 1 se in tree compare una radice, una potenza con l'esponente senza
 * x che non è un intero scritto, o un valore assoluto che non è tutto
 * l'argomento di un logaritmo: nei punti in cui la loro base, o il loro
 * argomento, vale zero il certificato non dice nulla (vedi sopra). */
static int node_has_root(const Node *tree, int x) {
    if (!tree) return 0;
    if (tree->kind == N_CALL && (tree->op == FN_ROOT || tree->op == FN_ABS)) return 1;
    if (tree->kind == N_CALL && (tree->op == FN_LN || tree->op == FN_LOG) && tree->a->kind == N_CALL && tree->a->op == FN_ABS)
        return node_has_root(tree->a->a, x) || node_has_root(tree->b, x);
    if (tree->kind == N_POW && !node_has_variable(tree->b, x) && tree->b->kind != N_NUM && !(tree->b->kind == N_NEG && tree->b->a->kind == N_NUM)) return 1;
    return node_has_root(tree->a, x) || node_has_root(tree->b, x) || node_has_root(tree->c, x);
}

/* Scrive in certificate_text il certificato di tipo kind ("derivative",
 * "antiderivative" o "integral") nella variabile x: order è il testo della
 * voce order (solo per una derivata, altrimenti NULL), function la funzione
 * da derivare o la primitiva, claim la derivata affermata o la funzione
 * integranda, lower, upper e value gli estremi e il valore di un integrale
 * (NULL altrimenti). Ritorna NULL, oppure il motivo per cui il certificato
 * non c'è. */
const char *calculus_certificate(const char *kind, int x, const char *order, const Node *function, const Node *claim,
                                        const Node *lower, const Node *upper, const Node *value) {
    certificate_length = 0;
    certificate_broken = 0;
    certificate_sequences = 0;
    if (x >= 128 || !isalpha(x)) return "la variabile non è una lettera";
    cert_real = x;
    cert_add("certificate %s\nvariable %c", kind, x);
    if (order) cert_add("\norder %s", order);
    if (lower) {
        cert_add("\nlower ");
        cert_node(lower);
        cert_add("\nupper ");
        cert_node(upper);
    }
    cert_add(order ? "\nfunction " : "\nintegrand ");
    cert_node(order ? function : claim);
    cert_add(order ? "\nderivative " : "\nprimitive ");
    cert_node(order ? claim : function);
    if (value) {
        cert_add("\nvalue ");
        cert_node(value);
    }
    const char *why = certificate_broken || certificate_sequences
                          ? "la notazione dei certificati delle derivate non ha arcoseno, arcocoseno e le successioni, o il testo è troppo lungo"
                          : NULL;

    /* I suggerimenti per i logaritmi: un fattore che non si sa scrivere si
     * toglie, e con lui il guasto che ha segnato. */
    for (int i = 0, written = 0; i < atom_count && written < MAX_BRICKS && !why; i++) {
        size_t before = certificate_length;
        if (!brick_fits(&atoms[i])) continue;
        cert_add("\nbrick ");
        cert_base(&atoms[i]);
        if (certificate_broken) {
            certificate_length = before;
            certificate_text[before] = '\0';
            certificate_broken = 0;
        } else {
            written++;
        }
    }
    cert_add("\nend\n");
    cert_real = 0;
    if (!why && certificate_broken) why = "il certificato è troppo lungo";
    return why;
}

/* Fa ricontrollare a checker.c il certificato appena scritto da
 * calculus_certificate(), che ha risposto why, e aggiorna *verdict, un
 * verdetto DIMOSTRATO o RISOLTO: vedi le risposte in testa a 27m. Se il
 * certificato è accettato e la funzione function (nella variabile x) ha
 * radici o valori assoluti, la nota del verdetto lo dice, dopo quella che
 * c'era già. Nel motivo i
 * due punti diventano virgole: in una riga RISOLTO dopo il primo ": " viene
 * la risposta, e gli script di tools/fuzz/ la cercano lì. */
void calculus_certify(Verdict *verdict, const char *why, const Node *function, int x) {
    static _Thread_local char problem[512], note[512];
    const char *text = certificate_text;
    if (!why) {
        CkAnswer answer = ck_check(&text, &why, checker_steps());
        if (answer == CK_ACCEPTED) {
            verdict->certificate = certificate_text;
            verdict->reason = NULL;
            if (node_has_root(function, x)) {
                snprintf(note, sizeof note, "%s%sil certificato non copre i punti in cui la base di una radice o di una potenza con l'esponente non "
                         "intero, o l'argomento di un valore assoluto, vale zero", verdict->note ? verdict->note : "", verdict->note ? "; " : "");
                verdict->note = note;
            }
            return;
        }
        if (answer == CK_REJECTED) {
            unjustified_steps++;
            snprintf(problem, sizeof problem, "il verificatore indipendente ha respinto il certificato, %s", why);
            *verdict = (Verdict){NOT_PROVED, 0, 0, 0, problem, NULL, NULL, NULL, NULL, NULL};
            return;
        }
        snprintf(problem, sizeof problem, "il verificatore non sa controllarlo, %s", why);
    } else {
        snprintf(problem, sizeof problem, "%s", why);
    }
    for (char *colon = problem; (colon = strchr(colon, ':')) != NULL;) *colon = ',';
    verdict->reason = problem;
}

/* 27k. CALCOLARE UNA DERIVATA
 *
 * \frac{d}{dx}\left( x^{2} \tan x \right), senza il segno di uguale, chiede
 * la derivata. La risposta è RISOLTO, con la derivata scritta:
 *
 *   27k-1. la derivata di ordine k, con le regole, confermata con la serie
 *          di Taylor in almeno un punto per ogni ordine (27h);
 *   27k-2. l'albero delle regole scritto come lo scriverebbe chi le ha
 *          appena applicate: senza fattori 1, addendi 0, esponenti 1 e 0 e segni
 *          doppi, con i conti tra interi fatti e il numero davanti al
 *          prodotto (node_tidy()): 2x \tan x + \frac{x^{2}}{\cos^{2} x};
 *   27k-3. il testo scritto si rilegge con il lettore del programma, come
 *          se l'avesse scritto l'utente, e il riletto deve avere lo stesso
 *          valore della derivata delle regole per due strade: con l'algebra
 *          esatta, dove sono definite (27a), e con i numeri, contro la
 *          derivata letta dalla serie di Taylor della funzione in tutti i
 *          punti di prova in cui le due si calcolano, almeno uno. Se non è
 *          così la risposta non si consegna.
 *
 * Perché basta una semplificazione leggera. La risposta deve essere giusta
 * e leggibile, non nella forma del libro: forme equivalenti sono infinite,
 * e confrontarle è compito di chi controlla (27a), non di chi scrive. Un
 * semplificatore completo (fattori comuni, identità goniometriche, forme
 * canoniche) sarebbe molto codice, che sbaglia in modi suoi e andrebbe
 * comunque ricontrollato; quello leggero fa solo passi che si vedono a
 * occhio, e ognuno lascia l'espressione definita esattamente dove lo era.
 *
 * Dove vale la risposta. Dove la funzione, la formula scritta e, per un
 * ordine più alto, le derivate prima di lei sono definite (27j): la nota
 * del verdetto lo dice, e per u^v aggiunge che la base deve essere
 * positiva. Dove la formula non ha valore la risposta non dice nulla, nemmeno
 * che la derivata non esiste (27l).
 */

/* Ritorna 1 e mette in *value il numero, se tree è un numero intero scritto. */
static int node_is_number(const Node *tree, long long *value) {
    if (tree->kind != N_NUM) return 0;
    *value = tree->value;
    return 1;
}

/* Se tree è un intero, o un prodotto il cui primo fattore da sinistra è un
 * intero, mette l'intero in *number e il resto del prodotto in *rest (NULL
 * se tree è solo il numero) e ritorna 1. I prodotti scritti da node_tidy()
 * hanno le parentesi a sinistra: (2 u) v. */
static int node_coefficient(Node *tree, long long *number, Node **rest) {
    Node *inner;
    if (node_is_number(tree, number)) { *rest = NULL; return 1; }
    if (tree->kind != N_MUL || !node_coefficient(tree->a, number, &inner)) return 0;
    *rest = inner ? node_new(N_MUL, inner, tree->b) : tree->b;
    return 1;
}

/* Ritorna 1 se tree ha un valore per ogni valore reale delle sue lettere:
 * numeri, lettere, somme, prodotti, potenze con esponente naturale scritto
 * come numero, seno, coseno, arcotangente, arcocotangente e valore assoluto
 * di espressioni così. È ciò che permette a node_tidy() di scrivere 0 al
 * posto di 0 u senza cambiare dove l'espressione è definita. Le potenze di
 * e non ci sono: se e fosse la variabile, e^{1/2} non sarebbe definita
 * ovunque. */
static int node_total(const Node *tree) {
    switch (tree->kind) {
    case N_NUM: case N_VAR: return 1;
    case N_NEG: return node_total(tree->a);
    case N_ADD: case N_SUB: case N_MUL: return node_total(tree->a) && node_total(tree->b);
    case N_POW:
        return tree->b->kind == N_NUM && tree->b->value >= 0 && node_total(tree->a);
    case N_CALL:
        return (tree->op == FN_SIN || tree->op == FN_COS || tree->op == FN_ARCTAN || tree->op == FN_ARCCOT || tree->op == FN_ABS) && node_total(tree->a);
    default: return 0;
    }
}

/* Ritorna il prodotto di number per rest (rest NULL: il solo numero). */
static Node *node_scaled(long long number, Node *rest) {
    if (!rest) return node_num(number);
    return number == 1 ? rest : node_new(N_MUL, node_num(number), rest);
}

/* 27k-2. Ritorna una copia di tree senza ciò che un libro non scriverebbe
 * (vedi sopra). Ogni passo conserva le condizioni di esistenza: per questo
 * 0 u diventa 0 solo se u ha un valore ovunque (node_total()), e a / (b / c)
 * resta com'è, perché a c / b perderebbe la condizione c diverso da zero. Le
 * altre riscritture spostano divisioni, segni e parentesi senza togliere
 * nessun denominatore: (a / b) c = a c / b, (a / b) / c = a / (b c),
 * a (b c) = (a b) c, -(-a) = a, a - (b + c) = a - b - c, e un numero in
 * comune tra numeratore e denominatore si semplifica, (6 u) / (4 v) =
 * (3 u) / (2 v). */
Node *node_tidy(const Node *tree) {
    long long p, q, product, top, bottom;
    Node *above, *below;
    int closed = 1;
    if (!tree || tree->kind == N_NUM || tree->kind == N_VAR) return (Node *)tree;
    Node *folded = node_fold(tree, &closed);
    if (folded->kind == N_NUM) return folded;
    Node *a = node_tidy(folded->a), *b = node_tidy(folded->b);
    int a_number = a && node_is_number(a, &p), b_number = b && node_is_number(b, &q);
    switch (folded->kind) {
    case N_NEG:
        if (a->kind == N_NEG) return a->a;
        if (a_number) return node_num(-p);
        break;
    case N_ADD: case N_SUB: {
        NodeKind other = folded->kind == N_ADD ? N_SUB : N_ADD;
        if (b_number && q == 0) return a;
        if (a_number && p == 0) return folded->kind == N_ADD ? b : node_tidy(node_new(N_NEG, b, NULL));
        if (b->kind == N_NEG) return node_new(other, a, b->a);
        if (b_number && q < 0) return node_new(other, a, node_num(-q));
        if (folded->kind == N_SUB && (b->kind == N_ADD || b->kind == N_SUB))
            return node_tidy(node_new(b->kind == N_ADD ? N_SUB : N_ADD, node_new(N_SUB, a, b->a), b->b));
        break;
    }
    case N_MUL:
        if (a_number && p == 1) return b;
        if (b_number && q == 1) return a;
        if ((a_number && p == 0 && node_total(b)) || (b_number && q == 0 && node_total(a))) return node_num(0);
        if (b_number && !a_number) return node_tidy(node_new(N_MUL, b, a));
        if (a_number && p < 0) return node_new(N_NEG, node_tidy(node_new(N_MUL, node_num(-p), b)), NULL);
        if (a->kind == N_NEG) return node_new(N_NEG, node_tidy(node_new(N_MUL, a->a, b)), NULL);
        if (b->kind == N_NEG) return node_new(N_NEG, node_tidy(node_new(N_MUL, a, b->a)), NULL);
        if (a_number && b->kind == N_MUL && node_is_number(b->a, &q) && !__builtin_mul_overflow(p, q, &product))
            return node_tidy(node_new(N_MUL, node_num(product), b->b));
        if (b->kind == N_DIV) return node_tidy(node_new(N_DIV, node_new(N_MUL, a, b->a), b->b));
        if (a->kind == N_DIV) return node_tidy(node_new(N_DIV, node_new(N_MUL, a->a, b), a->b));
        if (b->kind == N_MUL) return node_tidy(node_new(N_MUL, node_new(N_MUL, a, b->a), b->b));
        break;
    case N_DIV:
        if (b_number && q == 1) return a;
        if (a->kind == N_NEG) return node_new(N_NEG, node_tidy(node_new(N_DIV, a->a, b)), NULL);
        if (b->kind == N_NEG) return node_new(N_NEG, node_tidy(node_new(N_DIV, a, b->a)), NULL);
        if (a->kind == N_DIV) return node_tidy(node_new(N_DIV, a->a, node_new(N_MUL, a->b, b)));
        if (node_coefficient(a, &top, &above) && node_coefficient(b, &bottom, &below) && top && bottom) {
            long long common = (long long)gcd128(top, bottom);
            if (bottom < 0) common = -common;
            if (common != 1) return node_tidy(node_new(N_DIV, node_scaled(top / common, above), node_scaled(bottom / common, below)));
        }
        break;
    case N_POW:
        if (b_number && q == 1) return a;
        /* u^0, che la regola delle potenze lascia derivando u (27e), è 1
         * dove u ha un valore: ovunque, se u è totale. Senza, la derivata
         * seconda di x^2 y si scriveva 2 \cdot x^{0} \cdot y. */
        if (b_number && q == 0 && node_total(a)) return node_num(1);
        break;
    default:
        break;
    }
    return node_rebuilt(folded, a, b, folded->c);
}

/* 27n. LA SPIEGAZIONE DI UNA DERIVATA: UNA REGOLA ALLA VOLTA
 *
 * A che cosa serve. La risposta a \frac{d}{dx}(x^{2} \tan x) è una formula;
 * chi studia vuole vedere da dove viene: la derivata di x^{2}, quella di
 * \tan x, e la regola del prodotto che le mette insieme. derive() fa
 * proprio questo, un nodo dell'albero alla volta, dal più interno: qui se
 * ne registra il percorso, come passi della spiegazione (capitolo 40), uno
 * per ogni pezzo dell'espressione che contiene la variabile:
 *
 *     \frac{d}{dx}(pezzo) = derivata del pezzo,     con la regola usata.
 *
 * Ogni riga è un enunciato vero per conto suo, e si ricontrolla per conto
 * suo: il pezzo e la sua derivata si rileggono dal testo scritto, e vanno a
 * checker.c come certificato di una derivata (27m). Il verificatore deriva
 * il pezzo con regole sue, scritte un'altra volta, e confronta. È il
 * controllo più indipendente che c'è: una regola sbagliata in derive()
 * darebbe una riga che il verificatore respinge. Una riga respinta è un
 * errore del programma (unjustified_steps); una che il verificatore non sa
 * controllare (arcoseno, arcocoseno, somme) non è un errore, ma senza
 * controllo non si mostra, e con lei cade la spiegazione.
 *
 * Che cosa non c'è ancora: gli ordini oltre il primo (sarebbe la stessa
 * cosa ripetuta sulla derivata), le derivate dimostrate invece che
 * richieste, e la figura con la retta tangente in un punto.
 */

/* 27n. Ritorna 1 se checker.c accetta che la derivata rispetto a x
 * dell'espressione scritta in function sia quella scritta in derivative: i
 * due testi si rileggono con il lettore degli enunciati, e ciò che il
 * verificatore riceve è ciò che si stampa. Altrimenti ritorna 0 e annota
 * perché: explain_wrong se un testo non si rilegge o il verificatore
 * respinge, explain_broken se non lo sa controllare.
 *
 * Usa il deposito dei certificati: chi chiama non deve averne uno da
 * conservare. */
static int explain_derivative_line(const char *function, const char *derivative, int x) {
    const Node *f = parse_expression(function), *d = syntax_error ? NULL : parse_expression(derivative);
    if (syntax_error) { syntax_error = NULL; explain_wrong = 1; return 0; }
    const char *why = calculus_certificate("derivative", x, "1", f, d, NULL, NULL, NULL), *text = certificate_text;
    CkAnswer answer = why ? CK_UNSUPPORTED : ck_check(&text, &why, checker_steps());
    if (answer == CK_REJECTED) explain_wrong = 1;
    else if (answer != CK_ACCEPTED) explain_broken = 1;
    return answer == CK_ACCEPTED;
}

/* 27n. Registra i passi della derivata rispetto a x dell'espressione u, dai
 * pezzi più interni: un passo EXPLAIN_DERIVE per ogni nodo che contiene la
 * variabile e non è la variabile stessa, con il pezzo, la sua derivata
 * (derive(), ripulita come la risposta da node_tidy()) e la regola usata.
 * Un pezzo che compare due volte si scrive una volta. Ogni riga si registra
 * solo se checker.c la accetta (explain_derivative_line()). */
static void explain_rules(const Node *u, int x) {
    if (explain_wrong || explain_broken || !u || !node_has_variable(u, x) || u->kind == N_VAR) return;
    explain_rules(u->a, x);
    explain_rules(u->b, x);
    if (explain_wrong || explain_broken) return;

    /* La regola: la stessa scelta che fa derive() guardando il nodo. */
    const Node *inner = u->a;
    DerivativeRule rule;
    switch (u->kind) {
    case N_NEG: case N_ADD: case N_SUB: rule = RULE_SUM; break;
    case N_MUL: rule = node_has_variable(u->a, x) && node_has_variable(u->b, x) ? RULE_PRODUCT : RULE_FACTOR; break;
    case N_DIV: rule = node_has_variable(u->b, x) ? RULE_QUOTIENT : RULE_FACTOR; break;
    case N_POW:
        rule = !node_has_variable(u->b, x) ? RULE_POWER : !node_has_variable(u->a, x) ? RULE_EXPONENTIAL : RULE_TOWER;
        if (rule == RULE_EXPONENTIAL) inner = u->b;
        break;
    case N_CALL: rule = RULE_FUNCTION; break;
    default: explain_broken = 1; return;
    }

    /* Il pezzo e la sua derivata, scritti. */
    size_t start = proof_length;
    put_node(u, 0);
    const char *function = explain_piece(start);
    for (int i = 0; i < explanation.steps; i++)
        if (explanation.step[i].kind == EXPLAIN_DERIVE && strcmp(explanation.step[i].text[0], function) == 0) return;
    start = proof_length;
    put_node(node_tidy(derive(u, x)), 0);
    const char *derivative = explain_piece(start);
    if (failure || explain_broken) { failure = NULL; explain_broken = 1; return; }
    if (!explain_derivative_line(function, derivative, x)) return;
    ExplainStep *step = explain_step(EXPLAIN_DERIVE, 0);
    step->flag = rule;
    step->count = u->kind == N_CALL ? u->op : 0;
    step->group = (rule == RULE_POWER || rule == RULE_EXPONENTIAL || rule == RULE_FUNCTION) && inner->kind != N_VAR;
    step->text[0] = function;
    step->text[1] = derivative;
}

/* 27n. Registra in `explanation` la spiegazione della richiesta di derivare
 * f rispetto a x, la cui risposta scritta è answer: che cosa si chiede, una
 * riga per regola (explain_rules()), la risposta. Va chiamata prima di
 * scrivere il certificato del verdetto, perché usa lo stesso deposito, e
 * rimette com'era tutto il resto: la memoria, un errore annotato, i segnali
 * di memoria e pila finite. Se una riga non regge la spiegazione resta
 * vuota, e se è il verificatore a respingerla unjustified_steps sale. */
static void explain_derivative(const Node *f, int x, const char *answer) {
    Scratch mark = scratch_mark();
    const char *was = failure;
    int memory = work_allocation_failed, stack = stack_exhausted;
    explanation.steps = explanation.columns = explanation.lines = explanation.comparisons = 0;
    failure = NULL;
    explain_wrong = explain_broken = 0;
    explain_capture(1);
    explanation.variable = x;
    explanation.request = EXPLAIN_DERIVATIVE;
    explanation.equivalence = 0;
    ExplainStep *ask = explain_step(EXPLAIN_ASK, 0);
    size_t start = proof_length;
    put_node(f, 0);
    ask->text[0] = explain_piece(start);
    explain_rules(f, x);
    explain_step(EXPLAIN_ANSWER, 0)->text[0] = answer;

    /* Senza nemmeno una riga non c'è nulla da spiegare: la derivata di x. */
    if (explanation.steps < 3 || failure || work_allocation_failed != memory || stack_exhausted != stack) explain_broken = 1;
    if (explain_wrong) unjustified_steps++;
    if (explain_wrong || explain_broken) explanation.steps = 0;
    explain_capture(0);
    syntax_error = NULL;
    failure = was;
    work_allocation_failed = memory;
    stack_exhausted = stack;
    scratch_drop(mark);
}

/* 27k. Risolve la richiesta di calcolare la derivata di ordine order di f
 * rispetto a x, come descritto sopra, e ne ritorna il verdetto: verdict è
 * quello che prove_derivative() ha già preparato. */
static Verdict solve_derivative(Node *f, int x, int order, Verdict verdict) {
    static _Thread_local char answer[MAX_FORMULA], note[200];
    Node *direct[MAX_JET + 1] = {f};
    DerivativeCheck check;
    verdict.variable = 0;

    /* 27k-1. */
    int confirmed = derivatives_confirmed(direct, order, x, &check);
    if (confirmed < 1) {
        verdict.outcome = confirmed ? NOT_PROVED : UNSUPPORTED;
        verdict.reason = failure;
        return verdict;
    }

    /* 27k-2: la derivata scritta, nella dimostrazione e nella risposta. */
    proof_add("\\textbf{Solution.} By the rules of differentiation, the derivative of order $%d$ with respect to $%c$ is $", order, x);
    size_t from = proof_length;
    put_node(node_tidy(direct[order]), 0);
    size_t length = proof_length - from;
    proof_add("$.\n\n");
    if (failure || length >= sizeof answer || proof_length >= PROOF_BYTES - 1) {
        verdict.outcome = NOT_PROVED;
        verdict.reason = failure ? failure : "la derivata è troppo lunga per essere scritta e riletta";
        return verdict;
    }
    memcpy(answer, proof_text + from, length);
    answer[length] = '\0';

    /* 27k-3: la rilettura, e i due controlli. Una smentita dei numeri è un
     * errore del programma, nello scrivere o nel rileggere; un conto che non
     * riesce lascia solo la risposta senza conferma. */
    Node *reread = parse_expression(answer);
    int agreed = 0, contradicted = 0, readable = !syntax_error && !failure;
    Node *sampled = readable ? sample_tree(reread, x, 0, 0) : NULL;
    for (int p = 0; p < DERIVATIVE_POINTS && readable; p++) {
        Range claimed = sample_value(sampled, x, range_ratio(derivative_points[p].num, derivative_points[p].den));
        int agreement = numbers_agree(claimed, check.taylor[order][p]);
        contradicted |= agreement < 0;
        agreed += agreement > 0;
    }
    int sound = readable && !contradicted && agreed && !failure && derivative_identity(direct[order], reread, f, 0, 0, x);
    if (!sound) {
        if (contradicted || !readable) unjustified_steps++;
        failure = syntax_error = NULL;
        verdict.outcome = NOT_PROVED;
        verdict.reason = !readable      ? "la derivata scritta non si rilegge con il lettore del programma"
                         : contradicted ? "la derivata scritta, riletta dal testo, è smentita dalla serie di Taylor della funzione"
                                        : "non riesco a confermare la derivata scritta, riletta dal testo, con l'algebra esatta e con la serie di Taylor";
        return verdict;
    }
    proof_add("\\textbf{Check.} This formula, read back as text, has the value of the derivative given by the rules, by exact algebra "
              "where both are defined, and of the derivative read from the Taylor series of the function, computed with interval "
              "arithmetic at %d of the sample points. $\\Box$", agreed);

    /* Il verdetto, con la nota su dove vale. */
    snprintf(note, sizeof note, "%s%s", order == 1 ? "dove la funzione e la derivata sono definite" : "dove la funzione e le derivate fino a questa sono definite",
             node_has_tower(f, x) ? "; u^v con la variabile nella base e nell'esponente è e^{v \\ln u}, con u > 0" : "");
    verdict.outcome = SOLVED;
    verdict.method = "con le regole di derivazione";
    verdict.detail = answer;
    verdict.note = note;
    verdict.proof = proof_text;

    /* 27n. La spiegazione, una regola alla volta: prima del certificato del
     * verdetto, perché usa lo stesso deposito per far ricontrollare ogni
     * riga. Non cambia il verdetto. */
    if (explanations_wanted && order == 1) explain_derivative(f, x, answer);

    /* 27m. Il certificato dice ciò che dice il testo scritto, riletto. */
    char order_text[24];
    snprintf(order_text, sizeof order_text, "%d", order);
    calculus_certify(&verdict, calculus_certificate("derivative", x, order_text, f, reread, NULL, NULL, NULL), f, x);

    /* Un verdetto che il verificatore ha respinto non si spiega. */
    if (verdict.outcome != SOLVED) explanation.steps = 0;
    return verdict;
}

/* Prova a dimostrare l'enunciato su una derivata scritto in formula, con il
 * teorema in testa al capitolo. variable, has_base e base come per
 * prove_by_induction(); senza caso base una derivata n-esima parte da
 * n = 0, la funzione stessa. Se l'ordine è scritto come numero non c'è
 * induzione: basta 27a in quell'ordine, e il verdetto non ha una variabile
 * di induzione. Se formula non è scritta come una derivata il verdetto è
 * NON SUPPORTATO con il motivo NOT_A_DERIVATIVE.
 *
 * Il verdetto DIMOSTRATO porta il certificato di 27m, se il verificatore lo
 * accetta; altrimenti dice perché manca, in reason, e se il verificatore lo
 * respinge il verdetto è NON DIMOSTRATO. Svuota l'arena e la tabella degli
 * atomi: i risultati di chiamate precedenti non sono più validi. */
Verdict prove_derivative(const char *formula, int variable, int has_base, long long base) {
    static _Thread_local char text[320];
    Verdict verdict = {UNSUPPORTED, variable, has_base ? base : 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    DerivativeStatement statement;

    /* Ripartenza da zero per il nuovo enunciato, e parsing. */
    proof_reset();
    arena_used = arena_keep;
    atom_count = base_poly_count = atan_count = 0;
    failure = NULL;
    if (!parse_derivative_statement(formula, &statement)) { verdict.reason = NOT_A_DERIVATIVE; return verdict; }
    int x = statement.variable, fixed = !statement.order;
    Node *f = statement.function, *g = statement.formula;
    if (failure) { verdict.reason = failure; return verdict; }

    /* 27j. I segni di derivata dentro la funzione o la formula. */
    derivative_signs = 0;
    f = derivatives_expanded(f);
    g = derivatives_expanded(g);
    if (failure) { verdict.reason = failure; return verdict; }

    /* 27k. Senza la formula è una richiesta: calcolare la derivata. */
    if (!g) {
        if (!fixed) verdict.reason = "si calcola una derivata il cui ordine è scritto come numero; una formula per la derivata n-esima va scritta dopo il segno di uguale";
        else if (statement.times > MAX_DERIVATIVE_BASE) verdict.reason = "l'ordine di una derivata da calcolare deve essere al più 4";
        else return solve_derivative(f, x, (int)statement.times, verdict);
        return verdict;
    }

    /* L'ordine: la variabile di induzione, da base in su, oppure un numero. */
    if (fixed) {
        base = statement.times;
        verdict.variable = 0;
        verdict.method = "con le regole di derivazione";
    } else if (!has_base) {
        base = 0;
    }
    if (x == variable || (!fixed && (statement.order != variable || node_uses_letter(f, variable)))) {
        verdict.reason = "l'ordine di derivazione deve essere la variabile di induzione, e la funzione da derivare non deve contenerla";
        return verdict;
    }
    if (base < 0 || base > MAX_DERIVATIVE_BASE) { verdict.reason = "l'ordine di una derivata, o il caso base di una derivata n-esima, deve essere al più 4"; return verdict; }
    induction_var = variable;
    default_base = 1;
    domain_floor = base;

    /* Le derivate di f, una dopo l'altra, con le regole. Servono fino
     * all'ordine del caso base; quelle dopo sono per la verifica, e si
     * smette se diventano lunghe o se le regole non le sanno fare. */
    Node *direct[MAX_JET + 1] = {f}, *sampled[MAX_JET + 1];
    int orders = 0, wanted = (int)base + (fixed ? 0 : DIRECT_ORDERS);
    verdict.outcome = NOT_PROVED;
    while (orders < wanted && (orders < base || node_count(direct[orders]) < MAX_DERIVATIVE_NODES)) {
        Node *next = derive(direct[orders], x);
        if (failure && orders >= base) break;
        if (failure) {
            verdict.outcome = UNSUPPORTED;
            verdict.reason = failure;
            return verdict;
        }
        direct[++orders] = next;
    }
    failure = NULL;

    /* 27h. Ogni derivata delle regole contro la serie di Taylor di f, in
     * ogni punto di prova. Una smentita è un errore del programma; fino al
     * caso base ognuna deve essere confermata almeno in un punto. */
    DerivativeCheck check;
    for (int k = 0; k <= orders; k++) sampled[k] = sample_tree(direct[k], x, 0, 0);
    derivatives_check(&check, sampled, orders, x);
    if (failure) { verdict.reason = failure; return verdict; }
    if (check.wrong) {
        unjustified_steps++;
        verdict.reason = "una derivata calcolata con le regole di derivazione è smentita dalla serie di Taylor della funzione";
        return verdict;
    }
    for (int k = 1; k <= base; k++)
        if (!check.agree[k]) { verdict.reason = "non riesco a confermare con i numeri una derivata calcolata con le regole di derivazione"; return verdict; }

    /* 27i. Verifica indipendente, e smentita: la formula contro le derivate
     * delle regole e contro quelle della serie, in ogni punto di prova. Con
     * l'ordine fisso la lettera n, se c'è, è un parametro come gli altri. */
    int compared = 0, contradicted = 0;
    for (int k = (int)base; k <= orders; k++) {
        Node *right = sample_tree(g, x, fixed ? 0 : variable, k);
        for (int p = 0; p < DERIVATIVE_POINTS; p++) {
            Frac at = derivative_points[p];
            Range claimed = sample_value(right, x, range_ratio(at.num, at.den));
            int side, by_rules = range_side(range_sub(check.rules[k][p], claimed), &side);
            int by_series = range_side(range_sub(check.taylor[k][p], claimed), &side);
            if ((check.agree[k] >> p & 1) && by_rules && by_series) {
                snprintf(text, sizeof text, "%c = %lld/%lld", x, at.num, at.den);
                verdict.outcome = REFUTED;
                verdict.witness = k;
                verdict.detail = text;
                return verdict;
            }
            contradicted |= by_rules || by_series;
            if (numbers_agree(check.taylor[k][p], claimed) > 0) compared = 1;
        }
    }
    if (failure) { verdict.reason = failure; return verdict; }

    /* Una smentita da uno solo dei due conti non basta per il FALSO, ma
     * basta per non dire DIMOSTRATO: o la formula è sbagliata, o uno dei due
     * conti, e in nessuno dei due casi la dimostrazione va consegnata. */
    if (contradicted) {
        verdict.reason = "in un punto di prova la formula è di sicuro diversa da una derivata calcolata, ma le regole e la serie di Taylor non vi concordano abbastanza per dire FALSO";
        return verdict;
    }
    if (!compared) { verdict.reason = "non riesco a confermare con i numeri la formula, in nessuno dei punti di prova"; return verdict; }

    /* 27a. Il caso base: un'uguaglianza tra espressioni, senza n. */
    if (!derivative_identity(direct[base], fixed ? g : node_replace(g, variable, node_num(base)), f, variable, base, x)) {
        snprintf(text, sizeof text, "la derivata di ordine %lld, calcolata con le regole, non si riduce alla formula%s%s", base,
                 failure ? ": " : "", failure ? failure : "");
        failure = NULL;
        verdict.reason = text;
        return verdict;
    }
    if (fixed) proof_add("\\textbf{Proof.} By the rules of differentiation.\n\\begin{itemize}\n\\item ");
    else proof_add("\\textbf{Proof.} By induction on $%c$: it is enough that the formula is right for $%c = %lld$ and that its derivative with "
                   "respect to $%c$ is the formula for $%c + 1$.\n\\begin{itemize}\n\\item \\emph{Base case}, $%c = %lld$. ",
                   variable, variable, base, x, variable, variable, base);
    size_t opening = proof_length;
    if (base == 0) proof_add("The derivative of order $0$ is the function itself, $");
    else proof_add("Differentiating $%lld$ time%s with respect to $%c$ gives $", base, base > 1 ? "s" : "", x);
    Span left = {proof_length, 0};
    put_node(direct[base], 0);
    left.to = proof_length;
    proof_add("$, and the formula is $");
    Span right = put_side(g, fixed ? NULL : node_num(base));
    proof_add("$: the two are equal, because their difference reduces to $0$ by exact algebra.\n");

    /* Le derivate non si semplificano, e quella di ordine 4 può avere
     * migliaia di simboli: oltre MAX_FORMULA caratteri reread_equal() non la
     * rilegge e risponde "non confermata", che conterebbe come un passo
     * sbagliato (lo ha mostrato fuzz_derivatives.py con 1/(x/2 - 2)^2). Una
     * formula che non si può rileggere non si scrive: resta la frase, come
     * in 13g quando un valore è troppo lungo. */
    int sound = 1;
    if (left.to - left.from + right.to - right.from + 4 < MAX_FORMULA && proof_length < PROOF_BYTES - 1)
        sound = reread_equal(left, right, base) || reread_numbers(left, right, x);
    else {
        proof_cut(opening);
        proof_add("The derivative of order $%lld$ given by the rules of differentiation is too long to write here; its difference "
                  "from the formula reduces to $0$ by exact algebra.\n", base);
    }

    /* 27b. Il passo: la derivata della formula, confrontata anche lei con la
     * serie di Taylor per i primi due n (27h), e poi l'identità in n. */
    if (!fixed) {
        Node *slope = derive(g, x);
        if (failure) { verdict.outcome = UNSUPPORTED; verdict.reason = failure; return verdict; }
        for (long long k = base; k <= base + 1; k++) {
            Node *pair[2] = {sample_tree(g, x, variable, k), sample_tree(slope, x, variable, k)};
            derivatives_check(&check, pair, 1, x);
            if (failure) { verdict.reason = failure; return verdict; }
            if (check.wrong) {
                unjustified_steps++;
                verdict.reason = "la derivata della formula, calcolata con le regole di derivazione, è smentita dalla sua serie di Taylor";
                return verdict;
            }
            if (!check.agree[1]) { verdict.reason = "non riesco a confermare con i numeri la derivata della formula"; return verdict; }
        }
        Statement step = {slope, node_replace(g, variable, node_affine(1, variable, 1)), REL_EQ};
        proof_add("\\item \\emph{Inductive step}. Assume the statement for some $%c \\ge %lld$. The derivative of order $%c + 1$ is then the "
                  "derivative of the formula for $%c$, which the rules of differentiation give as $", variable, base, variable, variable);
        put_node(slope, 0);
        proof_add("$. It remains to prove that this is the formula for $%c + 1$: $", variable);
        put_comparison(step.lhs, REL_EQ, step.rhs);
        proof_add("$ for every $%c \\ge %lld$.\n", variable, base);
        atom_count = base_poly_count = atan_count = 0;
        Verdict inner = induct(&step, variable, 1, base, 1);
        if (inner.outcome != PROVED) {
            if (inner.outcome == REFUTED) snprintf(text, sizeof text, "la derivata della formula non è la formula per %c + 1: per %c = %lld sono diverse", variable, variable, inner.witness);
            else snprintf(text, sizeof text, "non riesco a dimostrare che la derivata della formula è la formula per %c + 1: %s", variable, inner.reason);
            verdict.reason = text;
            return verdict;
        }
    }
    proof_add("\\item \\emph{Check with numbers}. The derivative%s computed here agree%s with the formula at the sample points, and with "
              "the derivatives read from the Taylor series of the function, computed there with interval arithmetic.\n\\end{itemize}\n$\\Box$",
              orders > base ? "s" : "", orders > base ? "" : "s");
    if (!sound) {
        unjustified_steps++;
        verdict.reason = "una formula della dimostrazione, riletta dal testo, non è confermata";
        return verdict;
    }
    if (proof_length >= PROOF_BYTES - 1) { verdict.reason = "la dimostrazione è troppo lunga per essere scritta per intero"; return verdict; }
    verdict.outcome = PROVED;
    verdict.note = node_has_tower(f, x) ? "u^v con la variabile nella base e nell'esponente è inteso come e^{v ln u}, dove u > 0" : NULL;
    verdict.proof = proof_text;

    /* 27m. Il certificato: l'ordine è un numero, o la lettera dell'induzione
     * con il suo caso base. */
    char order_text[48];
    if (fixed) snprintf(order_text, sizeof order_text, "%lld", base);
    else snprintf(order_text, sizeof order_text, "%c base %lld", variable, base);
    calculus_certify(&verdict, calculus_certificate("derivative", x, order_text, f, g, NULL, NULL, NULL), f, x);
    return verdict;
}

/* 27l. I PUNTI IN CUI LE REGOLE NON DANNO LA DERIVATA
 *
 * Un segno espanso (27j) ha un valore nell'insieme E in cui la funzione g e
 * le sue derivate date dalle regole hanno tutte un valore, e lì vale la
 * derivata. Fuori da E, nei punti in cui g è definita, la derivata può
 * esistere o no: |x| non è derivabile in 0, x|x| sì, e le regole non danno
 * la derivata né all'una né all'altra. La tabella dei segni conta come
 * falso un confronto senza valore: nel secondo caso \forall x\ ((x|x|)' =
 * 2|x|) risulterebbe falso in x = 0, ed è vero.
 *
 * Il controllo. Per ogni segno si cerca, con la tabella dei segni, l'insieme
 * D dei punti in cui g ha un valore e l'espansione no. L'enunciato si decide
 * solo se ogni punto di D è un punto isolato con, accanto, un intervallo in
 * cui g non è definita: per esempio 0 per la radice di x. Lì la derivata
 * non esiste, perché chiede g definita in tutto un intorno del punto (la
 * derivata da una parte sola, che i libri chiamano destra o sinistra, è
 * un'altra cosa), e l'espansione, che lì non ha valore, dice il vero. Ogni
 * altro punto di D lascia l'enunciato non deciso, e il verdetto dice quali.
 * In un enunciato periodico basta un punto di D per non decidere: la sua
 * tabella è nella lettera t = tan(u/2), e il punto u = pi sta a parte.
 *
 * Perché la tabella qui è affidabile: è la stessa con i suoi controlli
 * indipendenti, e la condizione che le si chiede di risolvere è scritta con
 * le stesse espressioni dell'enunciato; se non sa risolverla, non sa
 * nemmeno decidere l'enunciato. */

/* Vedi la dichiarazione in testa a questo file. thesis è
 * l'enunciato, già controllato, di cui si sono espansi derivative_signs
 * segni. Lascia il testo della dimostrazione com'era. */
const char *derivative_doubt(const Formula *thesis) {
    static _Thread_local char reason[sizeof solution_text + 200];
    const Formula *q = thesis;
    while (q->kind == F_NOT) q = q->a;
    if (q->kind != F_FORALL && q->kind != F_EXISTS && q->kind != F_SOLVE)
        return "il segno di derivata è trattato negli enunciati con un quantificatore su una variabile reale, o in un insieme di soluzioni";
    size_t length = proof_length;
    int wanted = figures_wanted;
    const char *doubt = NULL;
    figures_wanted = 0;
    for (int i = 0; i < derivative_signs && !doubt; i++) {
        /* D: "g = g" vale dove g ha un valore, "non (e = e)" dove
         * l'espansione e non ce l'ha. */
        Formula *defined = formula_node(F_EQUAL, NULL, NULL, ""), *derived = formula_node(F_EQUAL, NULL, NULL, "");
        defined->left = defined->right = (Node *)expanded_function[i];
        derived->left = derived->right = (Node *)expanded_value[i];
        /* Nell'insieme dell'enunciato, con i suoi estremi e i punti tolti,
         * preso tra i reali anche se è di razionali: si guarda di più, non
         * di meno. */
        Formula *solve = formula_node(F_SOLVE, formula_node(F_AND, defined, formula_node(F_NOT, derived, NULL, ""), ""), NULL, "");
        solve->variable = q->variable;
        solve->numbers = q->numbers;
        solve->numbers.reals = 1;
        solve->numbers.integers = 0;
        Verdict inner = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
        decide_by_signs(solve, &inner);
        failure = NULL;
        if (inner.outcome != SOLVED) {
            snprintf(reason, sizeof reason, "non riesco a stabilire dove le regole di derivazione danno la derivata: %s", inner.reason ? inner.reason : "la tabella dei segni non decide");
            doubt = reason;
            break;
        }
        if (strncmp(inner.detail, "\\nexists", 8) == 0) continue;

        /* Ogni pezzo di D deve essere un punto, e accanto, da una parte,
         * g non deve avere un valore. */
        int isolated = !trig_on;
        Piece piece;
        for (int from = 0; isolated && sign_piece(solve->a, from, &piece); from = piece.last + 1) {
            int row = piece.first;
            isolated = piece.first == piece.last && row % 2 &&
                       (!sign_row[row - 1].inside || !sign_truth(defined, sign_row[row - 1].sign) ||
                        !sign_row[row + 1].inside || !sign_truth(defined, sign_row[row + 1].sign));
        }
        if (isolated) { derivative_edges = 1; continue; }
        snprintf(reason, sizeof reason, "la funzione è definita per %s, ma lì le regole di derivazione non ne danno la derivata: non so se vi è derivabile", inner.detail);
        doubt = reason;
    }
    figures_wanted = wanted;
    proof_cut(length);
    return doubt;
}
