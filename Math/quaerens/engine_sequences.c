/* MODULO engine_sequences: induzione su una disuguaglianza, successioni
 * definite per ricorrenza (capitoli 25-26).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_sequences.h, e
 * il resto è static. */
#include "engine_sequences.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"
#include "engine_intervals.h"
#include "engine_quantifiers.h"
#include "engine_sign_tables.h"
#include "engine_quantifiers_verdict.h"
#include "engine_derivatives.h"

/* =============================================================================
 * 25. INDUZIONE SU UNA DISUGUAGLIANZA
 * ============================================================================
 *
 * A che cosa serve. "La somma degli 1/sqrt(k), per k da 1 a n, è almeno
 * sqrt(n)"; "2^n >= n^3 da n = 10 in poi". Per un'uguaglianza l'ipotesi
 * induttiva dà il valore della somma, e basta sostituirlo (capitolo 13). Per
 * una disuguaglianza dà solo una stima: si può usare in un verso solo, e ciò
 * che resta da controllare non è più "questo polinomio è zero" ma "questa
 * espressione in n non è mai negativa". La prima domanda è algebra; la
 * seconda la sa decidere la tabella dei segni (18p), per ogni n reale.
 *
 * IL TEOREMA
 *
 * Sia D(n) il membro che l'enunciato dice maggiore meno l'altro, così che
 * l'enunciato sia "D(n) >= 0 per ogni intero n >= n0" (oppure "> 0").
 * Supponiamo che per un intero n1 >= n0:
 *
 *   25a. D(n) >= 0 per n = n0, ..., n1;
 *   25b. per ogni intero n >= n1 valga
 *
 *            U(n) D(n+1) = V(n) D(n) + P(n) T(n),
 *
 *        con U(n) diverso da zero, V(n)/U(n) >= 0, P(n)/U(n) >= 0 e
 *        T(n) > 0.
 *
 * Allora D(n) >= 0 per ogni intero n >= n0. Infatti fino a n1 lo dice 25a; e
 * se D(n) >= 0 per un n >= n1, dividendo l'identità per U(n) si ha
 * D(n+1) = (V/U) D(n) + (P/U) T, somma di due numeri non negativi.
 *
 * Con il segno stretto: se in 25a vale D(n) > 0 e in 25b vale V(n)/U(n) > 0,
 * allora D(n+1) > 0, perché il primo addendo è positivo. Quando V è il
 * polinomio nullo l'ipotesi non serve: D(n+1) = (P/U) T, e allora si chiede
 * P(n)/U(n) > 0.
 *
 * Le ipotesi contano tutte. Senza V/U >= 0 la stima D(n) >= 0 verrebbe
 * moltiplicata per un numero negativo e si rovescerebbe. Senza T > 0 il
 * segno di P/U non direbbe nulla del prodotto. Senza U diverso da zero
 * l'identità, in quell'n, non dice nulla di D(n+1): è 0 = 0.
 *
 * DA DOVE VIENE L'IDENTITÀ
 *
 * D(n) e D(n+1) si scrivono con gli stessi atomi (capitolo 13). Alcuni
 * atomi sono funzioni di n che hanno senso anche per n reale: n stesso, la
 * radice di n + 1. Altri no, e sono quelli che l'induzione deve far sparire:
 * una somma fino a n, n!, 2^n. Li chiamiamo discreti. Raccogliendo i monomi
 * discreti, i due numeratori sono
 *
 *     N  = c M + r        (D(n)   = N / Q)
 *     N' = c' M + r'      (D(n+1) = N' / Q')
 *
 * dove M è un monomio discreto, c e c' non contengono atomi discreti, e r,
 * r' sono ciò che resta. Allora, senza nessuna divisione,
 *
 *     c N' - c' N = c r' - c' r,    cioè    (c Q') D(n+1) = (c' Q) D(n) + (c r' - c' r).
 *
 * È l'identità del teorema, con U = c Q', V = c' Q, e P T = c r' - c' r,
 * purché quest'ultimo sia un polinomio senza atomi discreti (P) per un solo
 * monomio discreto (T), fatto di atomi positivi. Tre esempi:
 *
 *   - somma >= R(n): M è la somma, c = c' = 1, e P = (termine nuovo) -
 *     (R(n+1) - R(n)): "il termine che si aggiunge è almeno quanto cresce
 *     il secondo membro";
 *   - 2^n >= n^3: M = 2^n, c = 1, c' = 2, P = 2 n^3 - (n+1)^3: "raddoppiare
 *     n^3 dà più di (n+1)^3", vero da n = 4 in poi;
 *   - n! >= 2^n: M = n!, c = 1, c' = n + 1, T = 2^n, P = n - 1: è il
 *     confronto tra i due rapporti (n+1)!/n! e 2^{n+1}/2^n.
 *
 * Se D non contiene atomi discreti l'ipotesi non serve: U = Q', V = 0,
 * P = N', e l'enunciato in n + 1 è già una disuguaglianza nella sola n.
 *
 * Perché non si divide. Ricavare M dall'ipotesi, come fa il capitolo 13 per
 * le uguaglianze, vorrebbe dire dividere per c, e una frazione di polinomi
 * negli atomi semplifica n/n senza chiedersi se n è zero. Qui c resta al
 * suo posto, dentro U, e che U non si annulli lo dimostra la tabella dei
 * segni insieme al resto: per lei un confronto non vale dove un'espressione
 * non ha un valore.
 *
 * CHI DECIDE I SEGNI
 *
 *   - Di D(n) per n = n0, ..., n1: un conto esatto sui numeri (constant_side()).
 *   - Di V/U e di P/U per ogni n >= n1: la tabella dei segni, a cui si dà
 *     l'enunciato "per ogni n reale, n >= n1 implica V/U >= 0 e P/U >= 0".
 *     Vale per ogni reale, quindi per ogni intero. Il contrario no: se la
 *     tabella lo smentisce in un n non intero, qui non si conclude nulla.
 *   - Di T: atom_is_positive() (13c) per ognuno dei suoi atomi.
 *   - n1: il primo n da cui le due condizioni risultano vere nei valori
 *     calcolati. È solo una proposta, che la tabella poi dimostra o no.
 *
 * CHE COSA SI CONTROLLA, E CHE COSA NO
 *
 *   - L'enunciato deve essere definito per ogni n >= n0 (13c). Qui non ci
 *     sono parametri: una lettera diversa da n farebbe del passo una
 *     disuguaglianza in due variabili, che la tabella non tratta. La
 *     lettera e è il numero di Nepero, come nella tabella.
 *   - Verifica indipendente: D(n) viene calcolato davvero, con i numeri,
 *     per n = n0, ..., n0 + SEARCH_SPAN, senza passare né dall'identità né
 *     dalla tabella. Un valore del segno sbagliato è un controesempio, e il
 *     verdetto è FALSO.
 *   - L'identità scritta nella dimostrazione viene riletta dal testo e
 *     ricalcolata (come in 13g), a partire dai due membri dell'enunciato: i
 *     testi di U, V e P dati alla tabella sono quegli stessi caratteri.
 *   - Non c'è un certificato: la notazione di checker.c non ha né le
 *     disuguaglianze né le radici, e la tabella dei segni non ne emette. Il
 *     verdetto lo dice.
 *
 * Che cosa resta fuori: le disuguaglianze con parametri (Bernoulli con una
 * lettera), quelle in cui la somma compare al quadrato o sotto radice,
 * quelle il cui passo contiene un logaritmo di n insieme a una frazione,
 * quelle con tre o più monomi discreti (2^n + 3^n >= n). La risposta è NON
 * DIMOSTRATO o NON SUPPORTATO.
 */

/* Prototipo in avanti necessario: la base di un atomo è un polinomio, fatto
 * di atomi. */
static int poly_is_discrete(Poly p);

/* Ritorna 1 se l'atomo è discreto: una quantità che dipende da n e che ha
 * senso solo per n intero, o che comunque non è una funzione algebrica di n.
 * Sono le somme e i prodotti fino a n, i termini delle successioni per
 * ricorrenza, le potenze con n all'esponente, e le potenze e i logaritmi che
 * hanno per base una di queste. Non lo sono n, le radici di polinomi in n e
 * i numeri. */
static int atom_is_discrete(int atom) {
    const Atom *a = &atoms[atom];
    if (a->kind == ATOM_BIGOP || a->kind == ATOM_REC) return 1;
    if (a->kind != ATOM_POW && a->kind != ATOM_LN) return 0;
    if (a->kind == ATOM_POW && mono_depends_on_n(&a->exponent)) return 1;
    if (a->base == BASE_ATOM) return atom_is_discrete((int)a->id);
    return a->base == BASE_POLY && poly_is_discrete(base_polys[a->id]);
}

/* Ritorna la parte discreta del monomio m: il prodotto dei suoi fattori che
 * sono atomi discreti, ognuno con il suo esponente. */
static Mono mono_discrete(const Mono *m) {
    Mono part;
    part.count = 0;
    for (int i = 0; i < m->count; i++)
        if (atom_is_discrete(m->factor[i].atom)) part.factor[part.count++] = m->factor[i];
    return part;
}

/* Ritorna 1 se in p compare un atomo discreto. */
static int poly_is_discrete(Poly p) {
    for (int i = 0; i < p.count; i++)
        if (mono_discrete(&p.term[i].mono).count > 0) return 1;
    return 0;
}

/* Ritorna il coefficiente del monomio discreto `which` in p: la somma dei
 * termini di p la cui parte discreta è proprio which, divisi per which. Non
 * contiene atomi discreti. Con which = 1 è la parte di p senza atomi
 * discreti. */
static Poly discrete_coefficient(Poly p, const Mono *which) {
    Mono inverse = mono_pow(which, frac_int(-1));
    Term *buffer = terms_alloc(p.count);
    int used = 0;
    if (!buffer) return (Poly){0, NULL};
    for (int i = 0; i < p.count; i++) {
        Mono own = mono_discrete(&p.term[i].mono);
        if (mono_cmp(&own, which) != 0) continue;
        buffer[used] = p.term[i];
        buffer[used++].mono = mono_mul(&p.term[i].mono, &inverse);
    }
    return poly_finish(buffer, p.count, used);
}

/* Toglie gli atomi discreti dal denominatore di *r, se sono un monomio M
 * comune a tutti i suoi termini: numeratore e denominatore vengono divisi
 * per M, che finisce nel numeratore con gli esponenti cambiati di segno.
 * Così (2n+2)! / ((n+1)^2 n!^2) ha per denominatore il solo (n+1)^2. Il
 * valore non cambia dove M non è zero, cioè dove r è definita. Ritorna 0,
 * senza toccare *r, se il denominatore contiene atomi discreti in un altro
 * modo. */
static int rat_clear_discrete(Rat *r) {
    Mono common = mono_discrete(&r->den.term[0].mono);
    for (int i = 1; i < r->den.count; i++) {
        Mono own = mono_discrete(&r->den.term[i].mono);
        if (mono_cmp(&own, &common) != 0) return 0;
    }
    Term inverse;
    inverse.coef = num_int(1);
    inverse.mono = mono_pow(&common, frac_int(-1));
    r->num = poly_mul(r->num, poly_term(inverse));
    r->den = poly_mul(r->den, poly_term(inverse));
    return 1;
}

/* Mette in *side il segno del numero r e ritorna 1; ritorna 0 se non riesce
 * a stabilirlo. r è il valore di un'espressione senza lettere.
 *
 * Tre strade, dalla più precisa: il conto esatto di number_sign() (18p), che
 * tratta i razionali e le radici quadrate di interi e riconosce lo zero; il
 * test di annullamento del capitolo 12, per uno zero scritto con altri
 * atomi; gli intervalli del capitolo 24, che danno un segno certo quando il
 * numero non è zero. Un errore di questi conti (numeri troppo grandi) vuol
 * dire solo "non so". */
static int constant_side(Rat r, int *side) {
    const char *saved = failure;
    int above = 0, below = 0, known = number_sign(r, side);
    if (!known) {
        failure = saved;
        *side = 0;
        known = poly_vanishes(r.num);
        if (!known && range_side(poly_range(r.num), &above) && range_side(poly_range(r.den), &below)) {
            *side = above * below;
            known = 1;
        }
    }
    known = known && failure == saved;
    failure = saved;
    return known;
}

/* Ritorna D(n) per la disuguaglianza statement: il membro che l'enunciato
 * dice maggiore meno l'altro, con la variabile di induzione legata a n. */
static Rat inequality_gap(const Statement *statement, Rat n) {
    Rat gap = difference(statement, n);
    int upward = statement->relation == REL_GE || statement->relation == REL_GT;
    return upward ? gap : rat_add(rat_int(0), gap, 1);
}

/* L'identità del passo induttivo di una disuguaglianza (25b):
 * u D(n+1) = v D(n) + p t. I polinomi stanno nell'arena.
 * Invariante: u, v e p non contengono atomi discreti; ogni atomo di t è
 * discreto e positivo per ogni n dal caso base in su. */
typedef struct {
    Poly u, v, p;
    Mono t;        /* il monomio T; count == 0 vuol dire T = 1 */
} InequalityStep;

/* Cerca l'identità di 25b che elimina il monomio discreto `which` da
 * d = D(n) e d1 = D(n+1); con which NULL, quella che non usa l'ipotesi.
 * Ritorna 1 e riempie *step se l'identità ha la forma richiesta; 0 se which
 * non compare in D(n), o se ciò che resta non è un polinomio senza atomi
 * discreti per un monomio di atomi positivi da n = base in su. */
static int inequality_step(Rat d, Rat d1, const Mono *which, long long base, InequalityStep *step) {
    Poly rest = d1.num;
    step->u = d1.den;
    step->v = poly_const(num_int(0));
    if (which) {
        /* c N' - c' N: i termini con M si cancellano da soli. */
        Poly c = discrete_coefficient(d.num, which), c1 = discrete_coefficient(d1.num, which);
        if (c.count == 0) return 0;
        rest = poly_add(poly_mul(c, d1.num), poly_mul(c1, d.num), 1);
        step->u = poly_mul(c, d1.den);
        step->v = poly_mul(c1, d.den);
    }

    /* Un prodotto di polinomi non nulli può essere nullo, per le identità
     * tra atomi di term_reduce(): con U = 0 l'identità non dice nulla. */
    if (failure || step->u.count == 0) return 0;

    /* Ciò che resta: P per un solo monomio discreto T, positivo. */
    step->t.count = 0;
    if (rest.count > 0) step->t = mono_discrete(&rest.term[0].mono);
    for (int i = 1; i < rest.count; i++) {
        Mono own = mono_discrete(&rest.term[i].mono);
        if (mono_cmp(&own, &step->t) != 0) return 0;
    }
    for (int f = 0; f < step->t.count; f++)
        if (!atom_is_positive(step->t.factor[f].atom, base)) return 0;
    step->p = discrete_coefficient(rest, &step->t);

    /* La stessa identità con i segni cambiati, se serve perché U cominci con
     * un coefficiente positivo: si legge meglio, e non cambia né V/U né P/U. */
    if (step->u.term[0].coef.re.num < 0) {
        Poly zero = poly_const(num_int(0));
        step->u = poly_add(zero, step->u, 1);
        step->v = poly_add(zero, step->v, 1);
        step->p = poly_add(zero, step->p, 1);
    }
    return !failure;
}

/* Scrive il polinomio p nella dimostrazione e ritorna il pezzo scritto. */
static Span put_terms_span(Poly p) {
    Span span = {proof_length, 0};
    put_terms(p);
    span.to = proof_length;
    return span;
}

/* Mette in *side il segno che l'espressione tree prende quando la variabile
 * di induzione vale l'intero c, e ritorna 1; 0 se lì non è definita o se il
 * segno non si stabilisce. Gli atomi e la memoria del conto vengono tolti. */
static int tree_side(const Node *tree, long long c, int *side) {
    Scratch mark = scratch_mark();
    const char *saved = failure;
    env_count = 0;
    env_push(induction_var, rat_int(c));
    Rat value = eval(tree);
    env_count = 0;
    int known = failure == saved && constant_side(value, side);
    failure = saved;
    scratch_drop(mark);
    return known;
}

/* Prepara la domanda per la tabella dei segni: le condizioni di 25b
 * sull'identità step, da n = *start in su, con *start almeno `from`.
 *
 * Scrive i testi di U, V, P e T, li rilegge e controlla due cose. La prima:
 * che l'identità U D(n+1) = V D(n) + P T, con D scritto a partire dai due
 * membri dell'enunciato, riletta dal testo sia vera (il suo numeratore si
 * annulla). La seconda: da quale n, a partire da `from`, le condizioni
 * valgono nei valori già calcolati, cioè fino a `reached`; quell'n va in
 * *start. Poi mette in claim
 * le condizioni, in LaTeX: "V/U >= 0 e P/U >= 0", oppure le loro varianti
 * con il segno stretto (vedi il teorema). I testi sono scritti in fondo
 * alla dimostrazione in corso solo per poterli rileggere, e poi tolti.
 *
 * Ritorna NULL se riesce, altrimenti il motivo, in italiano. */
static const char *inequality_claim(const Statement *statement, const InequalityStep *step, int strict, long long from,
                                    long long reached, long long *start, char *claim, size_t size) {
    int upward = statement->relation == REL_GE || statement->relation == REL_GT, variable = induction_var;
    const Node *greater = upward ? statement->lhs : statement->rhs, *smaller = upward ? statement->rhs : statement->lhs;
    const Node *successor = node_affine(1, variable, 1);
    size_t opening = proof_length;
    char text[3][MAX_FORMULA], check[MAX_FORMULA];
    const char *problem = NULL;

    /* I testi: U, V, P, T, e i due membri in n + 1 e in n. */
    unwritable = 0;
    Span u = put_terms_span(step->u), v = put_terms_span(step->v), p = put_terms_span(step->p), t = {proof_length, 0};
    put_mono(&step->t);
    t.to = proof_length;
    Span side[4] = {put_side(greater, successor), put_side(smaller, successor), put_side(greater, NULL), put_side(smaller, NULL)};
    if (unwritable || failure || proof_length >= PROOF_BYTES - 1) problem = "il passo induttivo non si lascia scrivere come disuguaglianza nella sola variabile di induzione";

    /* L'identità, riletta. */
    int length = problem ? 0 : snprintf(check, sizeof check,
        "\\left(%.*s\\right) \\cdot \\left(\\left(%.*s\\right) - \\left(%.*s\\right)\\right) = "
        "\\left(%.*s\\right) \\cdot \\left(\\left(%.*s\\right) - \\left(%.*s\\right)\\right) + \\left(%.*s\\right)%s%.*s",
        (int)(u.to - u.from), proof_text + u.from, (int)(side[0].to - side[0].from), proof_text + side[0].from,
        (int)(side[1].to - side[1].from), proof_text + side[1].from, (int)(v.to - v.from), proof_text + v.from,
        (int)(side[2].to - side[2].from), proof_text + side[2].from, (int)(side[3].to - side[3].from), proof_text + side[3].from,
        (int)(p.to - p.from), proof_text + p.from, step->t.count ? " \\cdot " : "", (int)(t.to - t.from), proof_text + t.from);
    Statement identity;
    if (!problem && (length <= 0 || (size_t)length >= sizeof check)) problem = "il passo induttivo è troppo lungo da scrivere";
    if (!problem && !(parse_statement(check, &identity) && !failure &&
                      poly_vanishes(difference(&identity, rat_atom(atom_var(variable))).num) && !failure)) {
        unjustified_steps++;
        problem = "l'identità del passo induttivo, riletta dal testo, non è confermata";
    }

    /* I tre polinomi come espressioni, per calcolarli nei primi n. */
    Node *tree[3] = {NULL, NULL, NULL};
    const Span part[3] = {u, v, p};
    for (int i = 0; i < 3 && !problem; i++) {
        snprintf(text[i], sizeof text[i], "%.*s", (int)(part[i].to - part[i].from), proof_text + part[i].from);
        tree[i] = parse_expression(text[i]);
        if (syntax_error || failure) problem = "il passo induttivo, riletto dal testo, non è un'espressione";
    }
    proof_cut(opening);
    failure = NULL;
    if (problem) return problem;

    /* Da dove valgono le condizioni, nei valori calcolati. */
    int plain = step->v.count == 0;
    *start = from;
    for (long long c = from; c <= reached; c++) {
        int su = 0, sv = 0, sp = 0;
        int holds = tree_side(tree[0], c, &su) && tree_side(tree[1], c, &sv) && tree_side(tree[2], c, &sp) && su != 0 &&
                    (plain ? sp * su >= strict : sv * su >= strict && sp * su >= 0);
        if (!holds) *start = c + 1;
    }
    if (*start > reached) return "il passo induttivo non regge nei primi valori calcolati";

    /* Le condizioni. Con U = 1 le frazioni non servono, e con U = V = 1,
     * il caso di una somma, la prima condizione è 1 > 0 e si tace. */
    char ratio[2][MAX_FORMULA];
    for (int i = 0; i < 2; i++) {
        if (poly_is_one(step->u)) snprintf(ratio[i], sizeof ratio[i], "%s", text[i + 1]);
        else snprintf(ratio[i], sizeof ratio[i], "\\frac{%s}{%s}", text[i + 1], text[0]);
    }
    if (plain) length = snprintf(claim, size, "%s %s 0", ratio[1], strict ? ">" : "\\ge");
    else if (poly_is_one(step->u) && poly_is_one(step->v)) length = snprintf(claim, size, "%s \\ge 0", ratio[1]);
    else length = snprintf(claim, size, "%s %s 0 \\land %s \\ge 0", ratio[0], strict ? ">" : "\\ge", ratio[1]);
    return length > 0 && (size_t)length < size ? NULL : "il passo induttivo è troppo lungo da scrivere";
}

/* Scrive nella dimostrazione il caso n = c di una disuguaglianza: i due
 * membri con il numero al posto di n, i loro valori e quello di D(c). Con
 * first diverso da zero è il caso base, altrimenti uno dei casi successivi
 * controllati uno per uno. Ritorna 1 se ogni formula scritta, riletta (13g),
 * è confermata. */
static int put_inequality_case(const Statement *statement, long long c, int first) {
    const Node *side[2] = {statement->lhs, statement->rhs};
    int variable = induction_var, sound = 1, sign = 0;
    char prefix[64];
    Span text, value;
    proof_add(first ? "\\item \\emph{Base case}, $%c = %lld$. " : "\\item \\emph{Case} $%c = %lld$, checked directly. ", variable, c);
    for (int s = 0; s < 2; s++) {
        Rat low = side_value(side[s], rat_int(c));
        proof_add(s ? " and the right-hand side is $" : "The left-hand side is $");
        text = put_side(side[s], node_num(c));
        int bare = side[s]->kind == N_NUM || (side[s]->kind == N_VAR && side[s]->name == variable);
        if (!bare && put_value(" = ", low, &value)) sound &= reread_equal(text, value, c);
        proof_add("$");
    }

    /* D(c): il valore se si lascia scrivere, e un numero decimale vicino
     * quando il valore contiene radici o logaritmi. */
    Rat gap = inequality_gap(statement, rat_int(c));
    Num number;
    snprintf(prefix, sizeof prefix, ", so $D_{%lld} = ", c);
    constant_side(gap, &sign);
    if (put_value(prefix, gap, &value)) {
        Range near = range_div(poly_range(gap.num), poly_range(gap.den));
        double middle = (near.low + near.high) / 2;
        if (!rat_number(gap, &number) && range_known(near) && middle < 1e6 && middle > -1e6) proof_add(" \\approx %.4f", middle);
        proof_add(sign ? "$, a positive number.\n" : "$.\n");
    } else {
        proof_add(", and their difference $D_{%lld}$ is %s.\n", c, sign ? "positive" : "zero");
    }
    return sound;
}

/* Il lavoro di prove_inequality() che non riguarda la tabella dei segni,
 * sull'enunciato già analizzato: i primi valori (25a e la verifica
 * indipendente), "definito per ogni n", l'identità del passo (25b) e la
 * dimostrazione scritta, a cui manca solo la tabella.
 *
 * variable, has_base e base come per induct(). Se tutto riesce il verdetto è
 * PROVED, con la condizione che la tabella deve ancora dimostrare: la mette
 * in question, lunga al più size, come enunciato "per ogni n reale", e in
 * *start mette l'n da cui parte il passo (n1 nel teorema), che non è mai
 * minore di floor. Ogni altro verdetto è già quello definitivo. */
static Verdict inequality_plan(const Statement *statement, int variable, int has_base, long long base, long long floor,
                               long long *start, char *question, size_t size) {
    static _Thread_local char text[256];
    Verdict verdict = {UNSUPPORTED, variable, base, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    int strict = statement->relation == REL_GT || statement->relation == REL_LT;
    const char *relation = statement->relation == REL_GE ? "\\ge" : statement->relation == REL_LE ? "\\le" :
                           statement->relation == REL_GT ? ">" : "<";
    const char *sign = strict ? ">" : "\\ge";
    induction_var = variable;
    default_base = 1;
    domain_floor = has_base ? base : 1;

    /* D(n) e D(n+1), con gli stessi atomi. La prima valutazione fa nascere
     * gli atomi e calcola default_base, come in induct(). */
    Rat n = rat_atom(atom_var(variable));
    Rat d = inequality_gap(statement, n);
    if (failure) { verdict.reason = failure; return verdict; }
    if (!has_base) base = default_base;
    verdict.base = base;
    Rat d1 = inequality_gap(statement, rat_add(n, rat_int(1), 0));
    if (failure) { verdict.reason = failure; return verdict; }

    /* Nessun parametro: solo n, pi greco e il numero e. La lettera
     * ausiliaria non è dell'enunciato (vedi body_is_positive()). */
    for (int i = 0; i < atom_count; i++)
        if (atoms[i].kind == ATOM_VAR && atoms[i].id != variable && atoms[i].id != VAR_PI && atoms[i].id != VAR_SLACK && atoms[i].id != 'e') {
            verdict.reason = "le disuguaglianze con altre lettere oltre alla variabile di induzione non sono ancora supportate";
            return verdict;
        }

    /* 25a, e la verifica indipendente: il segno di D(c) nei primi valori. Un
     * conto che si ferma a un limite del programma chiude l'elenco dei
     * valori noti; un segno sbagliato è un controesempio. */
    Scratch mark = scratch_mark();
    long long reached = base - 1;
    verdict.outcome = NOT_PROVED;
    for (long long c = base; c <= base + SEARCH_SPAN; c++) {
        int side = 0;
        failure = NULL;
        undefined = 0;
        Rat gap = inequality_gap(statement, rat_int(c));
        if (failure && undefined) {
            snprintf(text, sizeof text, "per %c = %lld l'enunciato non è definito: %s", variable, c, failure);
            failure = NULL;
            verdict.reason = text;
            return verdict;
        }
        int known = !failure && constant_side(gap, &side);
        scratch_drop(mark);
        if (!known) break;
        if (side < 0 || (strict && side == 0)) {
            verdict.outcome = REFUTED;
            verdict.witness = c;
            return verdict;
        }
        reached = c;
    }
    failure = NULL;
    if (reached < base) { verdict.reason = "non riesco a stabilire il segno della differenza dei due membri nel caso base"; return verdict; }

    /* 13c. Definito per ogni n. */
    long long where = base;
    const char *why = NULL;
    int defined = defined_for_every(statement, base, &where, &why);
    scratch_drop(mark);
    if (defined != 1) {
        if (defined < 0) snprintf(text, sizeof text, "non riesco a stabilire che le espressioni dell'enunciato siano definite per ogni %c", variable);
        else snprintf(text, sizeof text, why == REWRITTEN ? "per %c = %lld %s" : "per %c = %lld l'enunciato non è definito: %s", variable, where, why);
        verdict.reason = text;
        return verdict;
    }

    /* 25b. I monomi discreti dei due numeratori. I denominatori non ne
     * devono avere. Tolto un monomio deve restarne al più uno: di solito
     * quindi sono due, ma possono essere di più se gli altri si cancellano,
     * come nella somma degli 1/2^k confrontata con 2 - 1/2^n. */
    enum { MAX_DISCRETE = 4 };
    Mono list[MAX_DISCRETE];
    int count = 0, many = !rat_clear_discrete(&d) || !rat_clear_discrete(&d1);
    const Poly numerator[2] = {d.num, d1.num};
    for (int s = 0; s < 2 && !many; s++)
        for (int i = 0; i < numerator[s].count && !many; i++) {
            Mono own = mono_discrete(&numerator[s].term[i].mono);
            int k = 0;
            while (k < count && mono_cmp(&list[k], &own) != 0) k++;
            if (own.count == 0 || k < count) continue;
            if (count == MAX_DISCRETE) many = 1; else list[count++] = own;
        }

    /* Si prova a eliminare ciascun monomio; senza monomi, l'identità che non
     * usa l'ipotesi. La prima che ha la forma giusta e regge nei primi
     * valori è quella che si scrive. */
    InequalityStep step;
    char claim[MAX_FORMULA];
    const char *problem = "il passo induttivo non si riduce a una disuguaglianza nella sola variabile di induzione";
    int found = 0;
    surd_powers = 1;
    for (int k = 0; k < (count ? count : 1) && !many && !found; k++) {
        failure = NULL;
        if (!inequality_step(d, d1, count ? &list[k] : NULL, base, &step)) continue;
        problem = inequality_claim(statement, &step, strict, base > floor ? base : floor, reached, start, claim, sizeof claim);
        found = !problem;
    }
    failure = NULL;
    int length = found ? snprintf(question, size, "\\forall %c \\in \\mathbb{R}\\ (%c \\ge %lld \\implies (%s))", variable, variable, *start, claim) : 0;
    if (!found || length <= 0 || (size_t)length >= size) {
        verdict.reason = found ? "il passo induttivo è troppo lungo da scrivere" : problem;
        return verdict;
    }

    /* La dimostrazione scritta: i casi da base a start, uno per uno. */
    int sound = 1, plain = step.v.count == 0, upward = statement->relation == REL_GE || statement->relation == REL_GT;
    const Node *successor = node_affine(1, variable, 1);
    proof_add("\\textbf{Proof.} By induction on $%c$. Let $D_{%c}$ be the %s-hand side minus the %s-hand side: the statement says "
              "that $D_{%c} %s 0$ for every integer $%c \\ge %lld$.\n\\begin{itemize}\n",
              variable, variable, upward ? "left" : "right", upward ? "right" : "left", variable, sign, variable, base);
    for (long long c = base; c <= *start; c++) sound &= put_inequality_case(statement, c, c == base);

    /* L'ipotesi, se serve, e ciò che va dimostrato. */
    if (plain) {
        proof_add("\\item \\emph{Inductive step}. Here the inductive hypothesis is not needed. For every $%c \\ge %lld$ we prove the statement for $%c + 1$: $",
                  variable, *start, variable);
    } else {
        proof_add("\\item \\emph{Inductive hypothesis}. Assume the statement for some $%c \\ge %lld$: $", variable, *start);
        put_side(statement->lhs, NULL);
        proof_add(" %s ", relation);
        put_side(statement->rhs, NULL);
        proof_add("$, that is $D_{%c} %s 0$.\n\\item \\emph{Inductive step}. We prove the statement for $%c + 1$: $", variable, sign, variable);
    }
    put_side(statement->lhs, successor);
    proof_add(" %s ", relation);
    put_side(statement->rhs, successor);
    proof_add("$, that is $D_{%c + 1} %s 0$.\n\\begin{itemize}\n", variable, sign);
    sound &= put_new_terms(base);

    /* L'identità: i fattori uguali a 1 e gli addendi nulli si tacciono. */
    proof_add("\\item Written with the same quantities, $D_{%c}$ and $D_{%c + 1}$ satisfy, by exact algebra, $", variable, variable);
    if (!poly_is_one(step.u)) { proof_add("\\left("); put_terms(step.u); proof_add("\\right) \\cdot "); }
    proof_add("D_{%c + 1} = ", variable);
    if (!plain && !poly_is_one(step.v)) { proof_add("\\left("); put_terms(step.v); proof_add("\\right) \\cdot "); }
    if (!plain) proof_add("D_{%c}", variable);
    if (step.p.count > 0 || plain) {
        proof_add(plain ? "\\left(" : " + \\left(");
        put_terms(step.p);
        proof_add(step.t.count ? "\\right) \\cdot " : "\\right)");
        put_mono(&step.t);
    }
    proof_add("$.\n");
    if (step.t.count > 0 && step.p.count > 0) {
        proof_add("\\item The factor $");
        put_mono(&step.t);
        proof_add("$ is positive: it is made of powers of positive numbers and of products of positive factors.\n");
    }

    /* La conclusione, che poggia sulla tabella dei segni scritta dopo. */
    proof_add("\\item The sign table below shows that $%s$ for every real number $%c \\ge %lld$. ", claim, variable, *start);
    if (!poly_is_one(step.u)) proof_add("There a comparison holds only where its sides have a value, so the factor of $D_{%c + 1}$ is not zero. ", variable);
    if (plain) proof_add("Hence $D_{%c + 1} %s 0$.\n", variable, sign);
    else proof_add("Since $D_{%c} %s 0$ by the inductive hypothesis, the identity gives $D_{%c + 1} %s 0$.\n", variable, sign, variable, sign);
    proof_add("\\end{itemize}\n\\item \\emph{The inequality of the inductive step}, for every real number $%c \\ge %lld$. ", variable, *start);
    if (!sound || proof_length >= PROOF_BYTES - 1) {
        if (!sound) unjustified_steps++;
        verdict.reason = "una formula della dimostrazione, riletta dal testo, non è confermata";
        return verdict;
    }
    verdict.outcome = PROVED;
    return verdict;
}

/* Chiede al metodo method l'enunciato question, scritto in LaTeX come lo
 * scriverebbe un utente, e ne ritorna il verdetto. È così che un capitolo ne
 * usa un altro che riparte da zero: i capitoli 25 e 26 la tabella dei segni
 * (ask_sign_table()), il capitolo 30 la tabella e i limiti del capitolo 29.
 *
 * Il metodo svuota l'arena, la tabella degli atomi e il testo della
 * dimostrazione. Chi chiama deve quindi aver finito con alberi e polinomi;
 * il testo già scritto invece viene messo da parte qui e, se il metodo
 * dimostra o risolve l'enunciato, ricomposto: prima quel testo, poi la
 * dimostrazione del metodo senza il quadratino con cui la chiude. Se insieme
 * non stanno nel testo, del metodo resta solo la frase short. Se il metodo
 * non dimostra e non risolve, il testo è quello che il metodo ha lasciato,
 * oppure, con keep, quello di prima. Il grafico non viene costruito:
 * sarebbe quello di un passo, non dell'enunciato. */
Verdict ask_method(Verdict (*method)(const char *), const char *question, const char *short_text, int keep) {
    static _Thread_local char written[PROOF_BYTES];
    static const char box[] = " $\\Box$";
    size_t length = proof_length, closing = sizeof box - 1;
    int wanted = figures_wanted;
    memcpy(written, proof_text, length + 1);
    figures_wanted = 0;
    Verdict answer = method(question);
    figures_wanted = wanted;
    if (answer.outcome != PROVED && answer.outcome != SOLVED) {
        if (keep) {
            memcpy(proof_text, written, length + 1);
            proof_length = length;
        }
        return answer;
    }

    size_t tail = proof_length;
    if (tail >= closing && strcmp(proof_text + tail - closing, box) == 0) proof_cut(tail -= closing);
    if (length + tail + 64 >= PROOF_BYTES) {
        proof_reset();
        proof_add("%s%s", written, short_text);
    } else {
        memmove(proof_text + length, proof_text, tail + 1);
        memcpy(proof_text, written, length);
        proof_length = length + tail;
    }
    return answer;
}

/* Chiede alla tabella dei segni (18p) l'enunciato question, "per ogni x
 * reale ...", con ask_method(). */
static Verdict ask_sign_table(const char *question) {
    return ask_method(prove_quantified, question, "The sign table, too long to be written here, shows that the condition holds on every row.", 0);
}

/* Prova a dimostrare per induzione la disuguaglianza scritta in formula, con
 * il metodo descritto in testa al capitolo. variable, has_base e base come
 * per prove_by_induction().
 *
 * Il verdetto DIMOSTRATO è senza certificato, e lo dice in reason. Svuota
 * l'arena e la tabella degli atomi: i risultati di chiamate precedenti non
 * sono più validi. */
Verdict prove_inequality(const char *formula, int variable, int has_base, long long base) {
    static _Thread_local char reason[400];
    Verdict verdict = {UNSUPPORTED, variable, base, 0, NULL, NULL, NULL, NULL, NULL, NULL}, refusal = verdict;
    long long start = 0;
    int asked = 0;

    /* Un tentativo per ogni n da cui far partire il passo: il primo lo
     * propone inequality_plan(); se la tabella smentisce il passo, che per
     * lei riguarda ogni numero reale, si riprova da un n più avanti, finché
     * ci sono casi già calcolati da mettere prima. Così 3^n >= 2 n^2 + 1 da
     * n = 0, il cui passo non vale tra 0 e 1, si dimostra con il passo da
     * n = 1. */
    for (long long floor = LLONG_MIN;; floor = start + 1) {
        Statement statement;
        char question[MAX_FORMULA];

        /* Ripartenza da zero per il nuovo enunciato, e parsing. */
        proof_reset();
        arena_used = arena_keep;
        atom_count = 0;
        base_poly_count = 0;
        atan_count = 0;
        failure = NULL;
        if (!parse_statement(formula, &statement)) { verdict.reason = syntax_error; return verdict; }

        /* 27j. I segni di derivata dentro le espressioni, prima di ogni conto. */
        derivative_signs = 0;
        statement.lhs = derivatives_expanded(statement.lhs);
        statement.rhs = derivatives_expanded(statement.rhs);
        if (failure) { verdict.reason = failure; return verdict; }
        verdict = inequality_plan(&statement, variable, has_base, base, floor, &start, question, sizeof question);
        surd_powers = 0;
        if (verdict.outcome != PROVED) return asked ? refusal : verdict;

        /* La tabella dei segni decide il passo. */
        Verdict table = ask_sign_table(question);
        asked = 1;
        if (table.outcome == PROVED) {
            proof_add("\n\\end{itemize}\n$\\Box$");
            verdict.reason = "il passo induttivo è deciso dalla tabella dei segni, e le disuguaglianze non hanno ancora una notazione nei certificati";
            verdict.proof = proof_text;
            return verdict;
        }

        /* Smentito in un numero reale: per gli interi non si conclude nulla,
         * e si riprova più avanti. Non deciso: ci si ferma. */
        if (table.outcome == REFUTED)
            snprintf(reason, sizeof reason, "il passo induttivo non vale per ogni %c reale da %lld in su: la tabella dei segni lo smentisce%s%s",
                     variable, start, table.detail ? " in " : "", table.detail ? table.detail : "");
        else
            snprintf(reason, sizeof reason, "la tabella dei segni non decide il passo induttivo, da %c = %lld in su: %s", variable, start, table.reason);
        refusal.outcome = table.outcome == UNSUPPORTED ? UNSUPPORTED : NOT_PROVED;
        refusal.base = verdict.base;
        refusal.reason = reason;
        if (table.outcome != REFUTED) return refusal;
    }
}

/* =============================================================================
 * 26. SUCCESSIONI DEFINITE PER RICORRENZA
 * ============================================================================
 *
 * A che cosa serve. "Sia a_0 = 0, a_1 = sin x e a_{n+1} = 2 cos x a_n -
 * a_{n-1}. Allora a_n = sin(n x)." La successione non è nel vocabolario
 * (capitolo 10): la definisce l'enunciato, con i primi valori e una regola
 * che dà ogni termine dai precedenti. L'enunciato arriva nella notazione di
 * parse_sequence_statement(): ipotesi, \implies, tesi. Le tesi trattate sono
 * di due tipi, ognuno con il suo teorema. Ci arrivano anche le iterate f^{n}
 * di un'applicazione di un enunciato con quantificatori (17s): fissato x, i
 * numeri f^{n}(x) sono una successione definita per ricorrenza (26c).
 *
 * LA SUCCESSIONE DICHIARATA
 *
 * Le ipotesi devono essere: d valori iniziali s_{i0}, ..., s_{i0+d-1}, e una
 * regola s_{n+r} = Phi, dove in Phi compaiono solo termini s_{n+j} con
 * r - d <= j < r (e n, e i parametri). d è l'ordine. La regola vale per ogni
 * n >= m0 = i0 - (r - d): il primo termine che definisce è s_{i0+d}, quello
 * dopo i valori iniziali. Se l'enunciato dice da quale n vale, deve dire
 * proprio m0. Ogni altra forma (valori iniziali mancanti o di troppo, un
 * termine come s_{2n}) è NON SUPPORTATO: non si indovina che cosa
 * l'enunciato intendesse.
 *
 * 26a. LA FORMULA CHIUSA: "allora s_n = C(n)"
 *
 * Teorema (una ricorrenza determina la successione). Se una successione c
 * ha gli stessi d valori iniziali di s e soddisfa la stessa regola per ogni
 * n >= m0, allora c_n = s_n per ogni n >= i0. Dimostrazione, per induzione
 * su N: i termini fino a i0+d-1 sono uguali per ipotesi; se sono uguali
 * tutti i termini prima di N = n + r, allora s_N = Phi(s_{N-1}, ...) =
 * Phi(c_{N-1}, ...) = c_N, perché Phi è la stessa espressione calcolata
 * negli stessi numeri.
 *
 * Con c_n = C(n) restano quindi da dimostrare due cose, nessuna delle quali
 * contiene più la successione:
 *
 *   - C(i0 + j) è il valore iniziale numero j, per j < d: un'uguaglianza tra
 *     espressioni senza n, che il test di annullamento decide;
 *   - C(n + r) = Phi con C(n + j) al posto di s_{n+j}, per ogni n >= m0:
 *     un'identità in n, dimostrata dall'induzione del capitolo 13 con tutti
 *     i suoi controlli (13c: definita per ogni n; 13e: i numeri).
 *
 * Il verdetto ha la riserva di ogni induzione del capitolo 13: vale per i
 * valori dei parametri in cui la formula chiusa è definita per ogni n.
 *
 * Verifica indipendente, e smentita. I termini s_{i0+d}, s_{i0+d+1}, ...
 * vengono calcolati uno dopo l'altro dalla regola, a partire dai valori
 * iniziali, e confrontati con C: un conto che non passa né dall'identità in
 * n né dall'induzione. Due numeri diversi sono un controesempio, e il
 * verdetto è FALSO con quell'n: così cade una formula sbagliata che
 * coincide con quella giusta nei primi valori.
 *
 * 26b. UNA STIMA: "allora s_n < 3 e s_n < s_{n+1}"
 *
 * Qui la regola deve essere s_{n+1} = Phi(s_n), senza n e senza parametri,
 * e le tesi confronti in cui compaiono solo s_n e s_{n+1}.
 *
 * Teorema (invariante). Sia I(a) una condizione sul numero reale a tale che
 *
 *   - I(s_{i0}) è vera;
 *   - per ogni reale a, se I(a) allora Phi(a) è definita, I(Phi(a)) è vera,
 *     e sono vere le tesi con a al posto di s_n e Phi(a) al posto di
 *     s_{n+1}.
 *
 * Allora per ogni n >= i0 il termine s_n esiste, I(s_n) è vera e le tesi
 * valgono. Dimostrazione: per induzione su n, I(s_n) è vera; quindi
 * s_{n+1} = Phi(s_n) è definita e soddisfa I, e le tesi in n sono il
 * secondo punto con a = s_n.
 *
 * L'invariante. Si prova prima con le tesi che parlano del solo s_n: se
 * s_n < 3 è una tesi, deve comunque essere dimostrata. Di solito non basta:
 * da a < 3 non segue che la radice di 6 + a esista. Allora si aggiunge ciò
 * che è vero del primo termine e che molte successioni conservano:
 * a >= s_{i0} (una successione crescente), poi a <= s_{i0}, poi "a ha il
 * segno di s_{i0}". Sono tentativi, ma l'invariante trovato non va creduto:
 * il secondo punto del teorema, che è un enunciato "per ogni a reale" in
 * una variabile, lo decide la tabella dei segni (18p), e il primo un conto
 * esatto.
 *
 * Verifica indipendente, e smentita. I primi termini vengono calcolati con
 * gli intervalli del capitolo 24, sostituendo la regola in se stessa, e le
 * tesi confrontate lì: un confronto certamente falso è un controesempio.
 *
 * Nessuno dei due teoremi ha una notazione nei certificati: il verdetto
 * DIMOSTRATO lo dice.
 *
 * Che cosa resta fuori: le tesi che non sono né una formula chiusa né una
 * stima (ln a_n = 2^n ln a_0, "è un intero pari"), le ricorrenze senza un
 * valore iniziale, e le formule chiuse la cui identità il capitolo 13 non
 * sa dimostrare, come quelle con una radice di cui serve il segno.
 */

/* Il motivo per cui un termine di una successione non si lascia sostituire:
 * il suo indice non è tra quelli attesi. Ha un nome perché chi prova una
 * sostituzione per vedere se riesce lo riconosce. */
static const char *const FOREIGN_TERM = "un termine della successione ha un indice che la ricorrenza non tratta";

/* Ritorna una copia di tree in cui la variabile name, dove è libera, è
 * sostituita dall'albero value, che non viene copiato. L'indice di una somma
 * nasconde, nel corpo, una variabile con lo stesso nome.
 *
 * Warning: value non deve contenere lettere che in tree sono indici di
 * somme, o verrebbero catturate. Qui value è un numero, n + j, oppure
 * un'espressione nella lettera di una successione. */
Node *node_replace(const Node *tree, int name, Node *value) {
    if (!tree) return NULL;
    if (tree->kind == N_VAR && tree->name == name) return value;
    Node *copy = node_new(tree->kind, node_replace(tree->a, name, value), node_replace(tree->b, name, value));
    copy->value = tree->value;
    copy->name = tree->name;
    copy->op = tree->op;
    copy->c = tree->kind == N_BIGOP && tree->name == name ? tree->c : node_replace(tree->c, name, value);
    return copy;
}

/* Ritorna una copia di tree in cui ogni termine s_{n + j} della successione
 * di nome name è sostituito da term[j - low], per j da low a low + count - 1;
 * n è la variabile di induzione. Se un termine ha un altro indice (s_0,
 * s_{2n}, s_{n + j} con j fuori dall'intervallo) fallisce con FOREIGN_TERM.
 * Gli alberi di term[] non vengono copiati. */
static Node *unfold_terms(const Node *tree, int name, long long low, int count, Node *const *term) {
    if (!tree || failure) return NULL;
    if (tree->kind == N_SEQ && tree->name == name) {
        long long a, c;
        if (!rat_affine(eval(tree->a), &a, &c) || a != 1 || c < low || c >= low + count) { fail(FOREIGN_TERM); return NULL; }
        return term[c - low];
    }
    Node *copy = node_new(tree->kind, unfold_terms(tree->a, name, low, count, term), unfold_terms(tree->b, name, low, count, term));
    copy->value = tree->value;
    copy->name = tree->name;
    copy->op = tree->op;
    copy->c = unfold_terms(tree->c, name, low, count, term);
    return copy;
}

/* Una successione dichiarata da un enunciato (vedi "La successione
 * dichiarata" in testa al capitolo): i valori iniziali e la regola, già
 * controllati. Gli alberi sono quelli dell'enunciato, nell'arena.
 * Invariante: 1 <= order <= MAX_ORDER, e in step compaiono solo termini
 * s_{n + j} con shift - order <= j < shift. */
typedef struct {
    int name;                    /* la lettera s */
    int order;                   /* d: quanti termini precedenti usa la regola */
    long long first;             /* i0: l'indice del primo valore iniziale */
    long long shift;             /* r: la regola dà s_{n + r} */
    long long since;             /* m0 = i0 - (r - d): il primo n in cui la regola vale */
    Node *initial[MAX_ORDER];    /* i valori di s_{i0}, ..., s_{i0 + d - 1} */
    Node *step;                  /* Phi: il valore di s_{n + r} */
} Declared;

/* Aggiorna *low e *high con il più piccolo e il più grande j dei termini
 * s_{n + j} della successione name che compaiono in tree; *found dice se ce
 * ne sono. Ritorna 0 se un termine ha un indice di un'altra forma. */
static int term_span(const Node *tree, int name, long long *low, long long *high, int *found) {
    if (!tree) return 1;
    if (tree->kind == N_SEQ && tree->name == name) {
        long long a, c;
        if (!rat_affine(eval(tree->a), &a, &c) || a != 1 || failure) return 0;
        if (!*found || c < *low) *low = c;
        if (!*found || c > *high) *high = c;
        *found = 1;
        return 1;
    }
    return term_span(tree->a, name, low, high, found) && term_span(tree->b, name, low, high, found) && term_span(tree->c, name, low, high, found);
}

/* Legge le ipotesi di statement come dichiarazione di una successione, con
 * `variable` variabile di induzione, e riempie *seq. Ritorna NULL se hanno
 * la forma richiesta (vedi la testa del capitolo), altrimenti il motivo, in
 * italiano. */
static const char *declared_read(const SequenceStatement *statement, int variable, Declared *seq) {
    long long index[MAX_GIVEN], low = 0, high = 0;
    Node *value[MAX_GIVEN];
    int values = 0, found = 0;
    memset(seq, 0, sizeof *seq);

    /* Ogni ipotesi: un valore iniziale s_{numero} = ..., o la regola
     * s_{n + r} = ..., una sola. */
    for (int i = 0; i < statement->givens; i++) {
        const Statement *given = &statement->given[i];
        long long a, c;
        if (given->lhs->kind != N_SEQ || (i > 0 && given->lhs->name != seq->name)) return "ogni ipotesi deve dare un termine della stessa successione, come a_{0} = 1 oppure a_{n + 1} = 2 a_{n}";
        seq->name = given->lhs->name;
        if (!rat_affine(eval(given->lhs->a), &a, &c) || failure || a < 0 || a > 1 || (a == 1 && seq->step)) return "le ipotesi devono essere i valori iniziali e una sola regola per il termine di indice n + r";
        if (a == 1) { seq->shift = c; seq->step = given->rhs; continue; }
        index[values] = c;
        value[values++] = given->rhs;
    }
    if (!seq->step) return "tra le ipotesi manca la regola che dà un termine dai precedenti";

    /* I termini che la regola usa: tutti prima di quello che definisce. */
    if (!term_span(seq->step, seq->name, &low, &high, &found) || !found || high >= seq->shift || seq->shift - low > MAX_ORDER)
        return "la regola deve dare il termine di indice n + r da quelli che lo precedono, al più quattro";
    seq->order = (int)(seq->shift - low);

    /* I valori iniziali: tanti quanti l'ordine, di indici consecutivi, e
     * senza termini della successione dentro. */
    if (values != seq->order) return "i valori iniziali devono essere tanti quanti i termini precedenti che la regola usa";
    seq->first = index[0];
    for (int i = 1; i < values; i++)
        if (index[i] < seq->first) seq->first = index[i];
    for (int i = 0; i < values; i++) {
        long long place = index[i] - seq->first;
        if (place >= values || seq->initial[place] || node_uses_letter(value[i], seq->name) || node_uses_letter(value[i], variable))
            return "i valori iniziali devono avere indici consecutivi, e non contenere né la lettera della successione né la variabile di induzione";
        seq->initial[place] = value[i];
    }

    /* Da dove vale la regola: se l'enunciato lo dice, deve dire questo. */
    seq->since = seq->first - (seq->shift - seq->order);
    if (statement->has_since && (statement->since_name != variable || statement->since != seq->since))
        return "la regola è data da un n diverso da quello che serve perché definisca tutti i termini dopo i valori iniziali";
    return NULL;
}

/* Ritorna 1 se in tree compare la variabile name, non come indice di una
 * somma né come nome di una successione. */
int node_has_variable(const Node *tree, int name) {
    if (!tree) return 0;
    if (tree->kind == N_VAR && tree->name == name) return 1;
    return node_has_variable(tree->a, name) || node_has_variable(tree->b, name) || node_has_variable(tree->c, name);
}

/* Ritorna 1 se un confronto con la relazione rel è vero quando la differenza
 * tra il primo e il secondo membro ha il segno side (-1, 0 o 1). */
static int relation_holds(Relation rel, int side) {
    switch (rel) {
    case REL_EQ: return side == 0;
    case REL_GE: return side >= 0;
    case REL_LE: return side <= 0;
    case REL_GT: return side > 0;
    default:     return side < 0;
    }
}

/* Scrive nella dimostrazione il confronto lhs rel rhs, in LaTeX, e ritorna
 * il pezzo scritto. */
Span put_comparison(const Node *lhs, Relation rel, const Node *rhs) {
    static const char *const sign[] = {[REL_EQ] = "=", [REL_GE] = "\\ge", [REL_LE] = "\\le", [REL_GT] = ">", [REL_LT] = "<"};
    Span span = {proof_length, 0};
    put_node(lhs, 0);
    proof_add(" %s ", sign[rel]);
    put_node(rhs, 0);
    span.to = proof_length;
    return span;
}

/* 26a. Dimostra la tesi "s_n = closed" per la successione seq, con il
 * teorema della formula chiusa (vedi la testa del capitolo): i valori
 * iniziali, i primi termini calcolati dalla regola, e la regola stessa per
 * induzione. Ritorna il verdetto, con la dimostrazione scritta; base è il
 * caso base da riportare.
 *
 * Azzera la tabella degli atomi prima dell'induzione, che la vuole per sé:
 * dopo questa chiamata i polinomi calcolati prima non valgono più. */
static Verdict prove_closed_form(const Declared *seq, Node *closed, int variable, long long base) {
    static _Thread_local char text[320];
    Verdict verdict = {NOT_PROVED, variable, base, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    long long low = seq->shift - seq->order;
    int sound = 1;
    const char *plural = seq->order > 1 ? "s" : "";

    proof_add("\\textbf{Proof.} A sequence is determined by its first value%s and by the rule that gives each term from the previous "
              "ones: two sequences with the same first value%s and the same rule are equal, by induction on the index. So it is "
              "enough to show that the formula $", plural, plural);
    put_node(closed, 0);
    proof_add("$ has the first value%s of $%c$ and satisfies its rule.\n\\begin{itemize}\n", plural, seq->name);

    /* I valori iniziali: un'uguaglianza senza n per ciascuno. */
    Rat window[MAX_ORDER];
    for (int j = 0; j < seq->order; j++) {
        long long at = seq->first + j;
        Num number;
        window[j] = side_value(seq->initial[j], rat_int(at));
        Rat gap = rat_add(side_value(closed, rat_int(at)), window[j], 1);
        if (failure) { verdict.outcome = UNSUPPORTED; verdict.reason = failure; return verdict; }
        if (!poly_vanishes(gap.num)) {
            /* Due numeri diversi smentiscono la tesi solo se è affermata
             * anche per questo indice. */
            if (rat_number(gap, &number) && at >= base) { verdict.outcome = REFUTED; verdict.witness = at; return verdict; }
            snprintf(text, sizeof text, "per %c = %lld la formula non si riduce al valore iniziale", variable, at);
            verdict.reason = text;
            return verdict;
        }
        proof_add("\\item \\emph{First value}, $%c = %lld$. The formula gives $", variable, at);
        Span formula = put_side(closed, node_num(at));
        proof_add("$, and $%c_{%lld} = ", seq->name, at);
        Span value = {proof_length, 0};
        put_node(seq->initial[j], 0);
        value.to = proof_length;
        proof_add("$: the two are equal.\n");
        sound &= reread_equal(formula, value, at);
    }

    /* Verifica indipendente, e smentita: i termini successivi, calcolati
     * uno dopo l'altro dalla regola con i termini precedenti legati a
     * variabili interne, e confrontati con la formula. Un conto che esce
     * dai limiti del programma ferma il confronto senza obiezioni. */
    Node *previous[MAX_ORDER];
    for (int j = 0; j < seq->order; j++) {
        previous[j] = node_new(N_VAR, NULL, NULL);
        previous[j]->name = VAR_TERM + j;
    }
    Node *rule = unfold_terms(seq->step, seq->name, low, seq->order, previous);
    long long last = seq->first + seq->order - 1;
    for (long long at = last + 1; at <= seq->first + seq->order + SEARCH_SPAN / 2 && !failure; at++) {
        Num number;
        undefined = 0;
        env_count = 0;
        env_push(variable, rat_int(at - seq->shift));
        for (int j = 0; j < seq->order; j++) env_push(VAR_TERM + j, window[j]);
        Rat term = eval(rule);
        env_count = 0;
        Rat gap = rat_add(term, side_value(closed, rat_int(at)), 1);
        if (failure && undefined) {
            snprintf(text, sizeof text, "per %c = %lld la regola o la formula non sono definite: %s", variable, at, failure);
            failure = NULL;
            verdict.reason = text;
            return verdict;
        }
        if (failure) break;
        if (!poly_vanishes(gap.num)) {
            if (rat_number(gap, &number) && at >= base) { verdict.outcome = REFUTED; verdict.witness = at; return verdict; }
            snprintf(text, sizeof text, "il termine di indice %lld, calcolato dalla regola, non si riduce alla formula", at);
            verdict.reason = text;
            return verdict;
        }
        for (int j = 0; j + 1 < seq->order; j++) window[j] = window[j + 1];
        window[seq->order - 1] = term;
        last = at;
    }
    failure = NULL;
    if (last < seq->first + seq->order) { verdict.reason = "non riesco a calcolare dalla regola nemmeno il primo termine dopo i valori iniziali"; return verdict; }
    proof_add("\\item \\emph{Check on the next terms}. The terms from $%c_{%lld}$ to $%c_{%lld}$, computed one after the other from the "
              "rule, coincide with the formula.\n", seq->name, seq->first + seq->order, seq->name, last);

    /* La regola, con la formula al posto dei termini: un'identità in n. */
    Node *term[MAX_ORDER];
    for (int j = 0; j < seq->order; j++) term[j] = node_replace(closed, variable, node_affine(1, variable, low + j));
    Statement identity = {node_replace(closed, variable, node_affine(1, variable, seq->shift)),
                          unfold_terms(seq->step, seq->name, low, seq->order, term), REL_EQ};
    if (failure) { verdict.outcome = UNSUPPORTED; verdict.reason = failure; return verdict; }
    proof_add("\\item \\emph{The rule}. With the formula in place of the terms of $%c$, the rule becomes $", seq->name);
    put_comparison(identity.lhs, REL_EQ, identity.rhs);
    proof_add("$, to be proved for every $%c \\ge %lld$.\n", variable, seq->since);
    atom_count = base_poly_count = atan_count = 0;
    Verdict inner = induct(&identity, variable, 1, seq->since, 1);
    if (inner.outcome != PROVED) {
        if (inner.outcome == REFUTED) snprintf(text, sizeof text, "la formula non soddisfa la regola: per %c = %lld i due membri sono diversi", variable, inner.witness);
        else snprintf(text, sizeof text, "non riesco a dimostrare che la formula soddisfa la regola: %s", inner.reason);
        verdict.reason = text;
        return verdict;
    }
    proof_add("\\end{itemize}\n$\\Box$");
    if (!sound) {
        unjustified_steps++;
        verdict.reason = "una formula della dimostrazione, riletta dal testo, non è confermata";
        return verdict;
    }
    verdict.outcome = PROVED;
    verdict.reason = "il teorema che una ricorrenza determina la successione non è nella notazione dei certificati";
    verdict.proof = proof_text;
    return verdict;
}

/* Quanti termini di una successione la regola 26b calcola con gli intervalli
 * per confrontarli con le tesi. Sono pochi perché l'albero di un termine
 * contiene quello del precedente tante volte quante la regola lo nomina. */
#define BOUND_TERMS 6

/* Quanti invarianti prova la regola 26b, uno per tentativo (vedi
 * bound_plan()). */
#define INVARIANTS 4

/* 26b. Prepara la dimostrazione delle tesi di statement, stime sui termini
 * della successione seq, con il teorema dell'invariante (vedi la testa del
 * capitolo). attempt, da 0 a INVARIANTS - 1, dice che cosa aggiungere alle
 * tesi per avere l'invariante: 0 niente, 1 "a >= primo termine", 2 "a <=
 * primo termine", 3 "a ha il segno del primo termine".
 *
 * Fa tutto tranne interrogare la tabella dei segni: il caso base, i primi
 * termini calcolati con gli intervalli, la dimostrazione scritta. Se riesce
 * il verdetto è PROVED e in question, lunga al più size, c'è l'enunciato
 * "per ogni a reale" che la tabella deve ancora dimostrare; ogni altro
 * verdetto è già quello definitivo. */
static Verdict bound_plan(const SequenceStatement *statement, const Declared *seq, int variable, long long base, int attempt,
                          char *question, size_t size) {
    static _Thread_local char text[320];
    Verdict verdict = {UNSUPPORTED, variable, base, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    const char *shape = "una stima sui termini si dimostra solo per una regola a_{n + 1} = f(a_n) in cui n non compare";
    int letter = seq->name;
    if (seq->order != 1 || seq->shift != 1) { verdict.reason = shape; return verdict; }

    /* Le espressioni nella lettera a: a stessa per s_n, Phi(a) per s_{n+1},
     * e il primo termine. In Phi(a) la variabile n non deve restare. */
    Node *now = node_new(N_VAR, NULL, NULL), *start = seq->initial[0];
    now->name = letter;
    Node *pair[2] = {now, unfold_terms(seq->step, letter, 0, 1, &now)}, *later[2] = {pair[1], NULL};
    if (failure || node_uses_letter(pair[1], variable)) { verdict.reason = failure ? failure : shape; return verdict; }

    /* La lettera della successione fa da variabile reale: se nell'enunciato
     * fosse anche un parametro, come in a_{n+1} = a a_n, dopo la
     * sostituzione i due non si distinguerebbero più. */
    int clash = node_has_variable(seq->step, letter);
    for (int i = 0; i < statement->claims; i++) clash |= node_has_variable(statement->claim[i].lhs, letter) || node_has_variable(statement->claim[i].rhs, letter);
    if (clash) { verdict.reason = "la lettera della successione compare anche come parametro"; return verdict; }

    /* Ogni tesi, in tre scritture: con a (solo se parla del solo s_n, e
     * allora entra nell'invariante), con Phi(a) al posto di a (l'invariante
     * dopo un passo), con a e Phi(a) (la tesi che nomina anche s_{n+1}). */
    Statement kept[MAX_CLAIMS + 1], next[MAX_CLAIMS + 1];
    int keeps = 0, nexts = 0, bound = 0;
    for (int i = 0; i < statement->claims && !failure; i++) {
        const Statement *claim = &statement->claim[i];
        Statement alone = {unfold_terms(claim->lhs, letter, 0, 1, pair), unfold_terms(claim->rhs, letter, 0, 1, pair), claim->relation};
        if (failure == FOREIGN_TERM) {
            failure = NULL;
            next[nexts++] = (Statement){unfold_terms(claim->lhs, letter, 0, 2, pair), unfold_terms(claim->rhs, letter, 0, 2, pair), claim->relation};
        } else {
            kept[keeps++] = alone;
            next[nexts++] = (Statement){unfold_terms(claim->lhs, letter, 0, 1, later), unfold_terms(claim->rhs, letter, 0, 1, later), claim->relation};
        }

        /* Tolti i termini, n non deve più comparire: una tesi come
         * s_n < n non è una condizione sul solo numero s_n. */
        bound |= !failure && (node_uses_letter(next[nexts - 1].lhs, variable) || node_uses_letter(next[nexts - 1].rhs, variable));
    }
    if (failure || bound) {
        verdict.reason = failure ? failure : "una stima sui termini si dimostra solo se n compare soltanto negli indici dei termini";
        return verdict;
    }
    if (attempt) {
        /* Ciò che si aggiunge: un confronto con il primo termine, o con
         * zero dalla parte in cui sta il primo termine. */
        int sign = 0;
        Node *bound = attempt < 3 ? start : node_num(0);
        Relation side = attempt == 1 ? REL_GE : attempt == 2 ? REL_LE : REL_GT;
        if (attempt == 3 && (!constant_side(side_value(start, rat_int(seq->first)), &sign) || sign == 0)) {
            verdict.outcome = NOT_PROVED;
            verdict.reason = "non trovo un invariante";
            return verdict;
        }
        if (sign < 0) side = REL_LT;
        kept[keeps++] = (Statement){now, bound, side};
        next[nexts++] = (Statement){pair[1], bound, side};
    }

    /* Il caso base, esatto: il primo termine soddisfa l'invariante. */
    verdict.outcome = NOT_PROVED;
    for (int i = 0; i < keeps; i++) {
        int side = 0;
        Rat gap = rat_add(side_value(node_replace(kept[i].lhs, letter, start), rat_int(seq->first)),
                          side_value(node_replace(kept[i].rhs, letter, start), rat_int(seq->first)), 1);
        if (failure || !constant_side(gap, &side)) {
            verdict.reason = failure ? failure : "non riesco a stabilire se il primo termine soddisfa le tesi";
            failure = NULL;
            return verdict;
        }
        if (!relation_holds(kept[i].relation, side)) {
            /* Un controesempio, se la tesi è affermata anche per il primo
             * termine; altrimenti l'invariante non parte, e basta. */
            if (seq->first >= base) { verdict.outcome = REFUTED; verdict.witness = seq->first; }
            else verdict.reason = "il primo termine non soddisfa le tesi, che sono affermate solo da un indice successivo";
            return verdict;
        }
    }

    /* Verifica indipendente, e smentita: i primi termini con gli intervalli
     * (capitolo 24), ognuno come albero in cui la regola è sostituita in se
     * stessa. Conta solo un confronto certamente falso. */
    Node *term = start;
    for (long long at = seq->first; at < seq->first + BOUND_TERMS; at++) {
        Node *both[2] = {term, unfold_terms(seq->step, letter, 0, 1, &term)};
        for (int i = 0; i < statement->claims; i++) {
            const Statement *claim = &statement->claim[i];
            int nowhere = 0, side = 0;
            Range gap = range_sub(node_range(unfold_terms(claim->lhs, letter, 0, 2, both), 0, range_none(), &nowhere),
                                  node_range(unfold_terms(claim->rhs, letter, 0, 2, both), 0, range_none(), &nowhere));
            if (failure || nowhere) {
                snprintf(text, sizeof text, "per %c = %lld un termine o una tesi non sono definiti", variable, at);
                failure = NULL;
                verdict.reason = text;
                return verdict;
            }
            if (at >= base && range_side(gap, &side) && !relation_holds(claim->relation, side)) {
                verdict.outcome = REFUTED;
                verdict.witness = at;
                return verdict;
            }
        }
        term = both[1];
    }

    /* I testi per la tabella: l'invariante, e ciò che ne deve seguire. */
    char hypothesis[MAX_FORMULA] = "", thesis[MAX_FORMULA] = "";
    size_t opening = proof_length;
    int fits = 1;
    for (int i = 0; i < keeps + nexts; i++) {
        const Statement *part = i < keeps ? &kept[i] : &next[i - keeps];
        char *into = i < keeps ? hypothesis : thesis;
        size_t used = strlen(into);
        Span span = put_comparison(part->lhs, part->relation, part->rhs);
        int written = snprintf(into + used, MAX_FORMULA - used, "%s%.*s", used ? " \\land " : "", (int)(span.to - span.from), proof_text + span.from);
        fits &= written > 0 && (size_t)written < MAX_FORMULA - used;
    }
    proof_cut(opening);
    int length = keeps ? snprintf(question, size, "\\forall %c \\in \\mathbb{R}\\ ((%s) \\implies (%s))", letter, hypothesis, thesis)
                       : snprintf(question, size, "\\forall %c \\in \\mathbb{R}\\ (%s)", letter, thesis);
    if (!fits || length <= 0 || (size_t)length >= size) { verdict.reason = "il passo induttivo è troppo lungo da scrivere"; return verdict; }

    /* La dimostrazione scritta, a cui manca solo la tabella. */
    proof_add("\\textbf{Proof.} By induction on $%c$, with an invariant: a condition $I(%c)$ on a real number $%c$ that the first term "
              "satisfies and that the rule preserves. ", variable, letter, letter);
    if (keeps) proof_add("Here $I(%c)$ is $%s$.\n\\begin{itemize}\n\\item \\emph{Base case}, $%c = %lld$. The first term is $%c_{%lld} = ",
                         letter, hypothesis, variable, seq->first, letter, seq->first);
    else proof_add("Here no condition is needed: $I(%c)$ is always true.\n\\begin{itemize}\n\\item \\emph{Base case}, $%c = %lld$. The first term is $%c_{%lld} = ",
                   letter, variable, seq->first, letter, seq->first);
    put_node(start, 0);
    proof_add(keeps ? "$, and it satisfies $I$: the comparisons are between numbers.\n" : "$.\n");
    proof_add("\\item \\emph{Inductive step}. Assume that $%c_{%c}$ exists and satisfies $I$ for some $%c \\ge %lld$, and write $%c$ for it: "
              "the next term is $%c_{%c + 1} = ", letter, variable, variable, seq->first, letter, letter, variable);
    put_node(pair[1], 0);
    proof_add("$. The sign table below shows that for every real number $%c$ %s $%s$. A comparison holds only where its sides have a "
              "value: so $%c_{%c + 1}$ exists, it satisfies $I$, and the claims hold for this $%c$.\n",
              letter, keeps ? "that satisfies $I$:" : ":", thesis, letter, variable, variable);
    proof_add("\\item \\emph{Check on the first terms}. The terms from $%c_{%lld}$ to $%c_{%lld}$, computed with guaranteed error bounds, "
              "do not contradict the claims.\n\\item \\emph{The condition of the inductive step}, for every real number $%c$. ",
              letter, seq->first, letter, seq->first + BOUND_TERMS - 1, letter);
    verdict.outcome = PROVED;
    return verdict;
}

/* Prova a dimostrare l'enunciato su una successione definita per ricorrenza
 * scritto in formula, nella notazione di parse_sequence_statement(), con i
 * teoremi 26a e 26b. variable, has_base e base come per
 * prove_by_induction(): la tesi è affermata per ogni n dal caso base in su,
 * che in sua assenza è l'indice del primo valore iniziale.
 *
 * Il verdetto DIMOSTRATO è senza certificato, e dice perché in reason.
 * Svuota l'arena e la tabella degli atomi: i risultati di chiamate
 * precedenti non sono più validi. */
Verdict prove_sequence(const char *formula, int variable, int has_base, long long base) {
    static _Thread_local char reason[400];
    Verdict verdict = {UNSUPPORTED, variable, base, 0, NULL, NULL, NULL, NULL, NULL, NULL}, refusal = verdict;

    /* Per una stima, un tentativo per ogni invariante (26b): la tabella dei
     * segni riparte da zero, quindi ogni volta si rilegge l'enunciato. Per
     * una formula chiusa (26a) basta il primo giro. */
    for (int attempt = 0;; attempt++) {
        SequenceStatement statement;
        Declared seq;
        char question[MAX_FORMULA];

        /* Ripartenza da zero per il nuovo enunciato, e parsing. */
        proof_reset();
        arena_used = arena_keep;
        atom_count = base_poly_count = atan_count = 0;
        failure = NULL;
        induction_var = variable;
        default_base = domain_floor = 1;
        if (!parse_sequence_statement(formula, &statement)) { verdict.reason = syntax_error; return verdict; }
        const char *problem = failure ? failure : declared_read(&statement, variable, &seq);
        if (!problem && has_base && base < seq.first) problem = "la tesi parte da un indice che viene prima dei valori iniziali";
        if (problem) { verdict.reason = problem; return verdict; }
        if (!has_base) base = seq.first;

        /* 26a. Una sola tesi, "s_n = formula" o "formula = s_n", con la
         * formula senza termini della successione. */
        const Statement *claim = &statement.claim[0];
        for (int side = 0; side < 2 && statement.claims == 1 && claim->relation == REL_EQ; side++) {
            Node *term = side ? claim->rhs : claim->lhs, *closed = side ? claim->lhs : claim->rhs;
            long long a, c;
            if (term->kind == N_SEQ && term->name == seq.name && rat_affine(eval(term->a), &a, &c) && a == 1 && c == 0 &&
                !node_uses_letter(closed, seq.name))
                return prove_closed_form(&seq, closed, variable, base);
        }

        /* 26b. Stime: l'invariante, poi la tabella dei segni. */
        verdict = bound_plan(&statement, &seq, variable, base, attempt, question, sizeof question);
        if (verdict.outcome != PROVED) return verdict.outcome == REFUTED || !attempt ? verdict : refusal;
        Verdict table = ask_sign_table(question);
        if (table.outcome == PROVED) {
            proof_add("\n\\end{itemize}\n$\\Box$");
            verdict.reason = "il passo induttivo è deciso dalla tabella dei segni, e le successioni dichiarate non hanno una notazione nei certificati";
            verdict.proof = proof_text;
            return verdict;
        }

        /* Smentito: l'invariante provato non si conserva, e se ne prova un
         * altro. Non deciso: ci si ferma. */
        if (table.outcome == REFUTED)
            snprintf(reason, sizeof reason, "nessun invariante tra quelli provati si conserva: la tabella dei segni smentisce l'ultimo%s%s",
                     table.detail ? " in " : "", table.detail ? table.detail : "");
        else
            snprintf(reason, sizeof reason, "la tabella dei segni non decide il passo induttivo: %s", table.reason);
        refusal.outcome = table.outcome == UNSUPPORTED ? UNSUPPORTED : NOT_PROVED;
        refusal.base = base;
        refusal.reason = reason;
        if (table.outcome != REFUTED || attempt == INVARIANTS - 1) return refusal;
    }
}

/* 26c. LE ITERATE DI UN'APPLICAZIONE
 *
 * A che cosa serve. "f(x) = 2 + 3x, f^{1} = f e f^{n+1} = f \circ f^{n}:
 * allora f^{n}(x) = (3^{n} - 1) + 3^{n} x per ogni n e ogni x." Fissato x,
 * i numeri s_n = f^{n}(x) sono una successione definita per ricorrenza: s_c =
 * f(x), e s_{n+1} = f^{n+1}(x) = f(f^{n}(x)) = f(s_n), cioè la regola di f
 * con s_n al posto della sua variabile. È ciò che dicono le due ipotesi, e
 * niente di più: l'enunciato sulle iterate è quello sulla successione, e lo
 * dimostra 26a, con x come parametro.
 *
 * Perché il passaggio è lecito, e che cosa serve:
 *
 *   - la regola di f deve valere in s_n: s_n è un valore di f, quindi sta
 *     nel codominio, e il codominio deve stare nel dominio (numbers_subset());
 *     che i valori di f stiano nel codominio lo dimostra 18m;
 *   - la tesi deve essere per ogni n da c in su e per ogni x di una parte del
 *     dominio, f^{n}(x) = E, con E senza iterate;
 *   - 26a vale per i valori del parametro in cui la formula è definita per
 *     ogni n: con le divisioni di E e della regola soltanto per numeri non
 *     c'è riserva, e così si chiede. Per lo stesso motivo una smentita di
 *     26a vale anche qui: per un n fissato E - f^{n}(x) è un polinomio in x
 *     non nullo, che si annulla in un numero finito di punti, e l'insieme di
 *     x è infinito.
 *
 * La successione si scrive nella notazione di parse_sequence_statement(),
 * con una lettera nuova, e la si passa a prove_sequence(): da lì in poi è un
 * enunciato del capitolo 26 come gli altri, con i suoi controlli. */

/* Ritorna 1 se in node compare un'iterata di un'applicazione. */
static int node_iterates(const Node *node) {
    return node && ((node->kind == N_APPLY && node->c) || node_iterates(node->a) || node_iterates(node->b) || node_iterates(node->c));
}

/* 26c. Decide la tesi thesis di un enunciato che definisce le iterate di
 * un'applicazione, come descritto in testa al paragrafo, e ne ritorna il
 * verdetto. Svuota l'arena, come prove_sequence(): al ritorno le applicazioni
 * e la tesi non valgono più. */
Verdict decide_iterates(const Formula *thesis) {
    static _Thread_local char sequence[MAX_FORMULA], prefix[PROOF_BYTES / 4], shown[3][MAX_FORMULA / 3];
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, "per induzione, sulle iterate come successione", NULL, NULL};
    verdict.reason = "le iterate f^{n} si dimostrano in un'uguaglianza f^{n}(x) = E, per ogni n dal primo indice e per ogni x, "
                     "con f data da una regola sola che manda il codominio nel dominio";

    /* La forma: due "per ogni", n e x, e un'uguaglianza con f^{n}(x) da una
     * parte. */
    const Formula *outer = thesis, *inner = thesis->kind == F_FORALL ? thesis->a : NULL;
    const Formula *equation = inner && inner->kind == F_FORALL ? inner->a : NULL;
    if (!equation || equation->kind != F_EQUAL) return verdict;
    const Node *term = equation->left, *closed = equation->right;
    if (!(term->kind == N_APPLY && term->c)) { term = equation->right; closed = equation->left; }
    if (term->kind != N_APPLY || !term->c || term->c->kind != N_VAR || term->a->kind != N_VAR || node_iterates(closed)) return verdict;
    const Formula *index = outer->variable == term->c->name ? outer : inner, *point = index == outer ? inner : outer;
    if (index->variable != term->c->name || point->variable != term->a->name) return verdict;
    const Map *map = map_find(term->name);
    if (!map || !map->body || map->cases || map->binary || map->partner || statement_parameter_count ||
        map->iterate_from != map->step_from || !index->numbers.integers || !index->numbers.bounded || index->numbers.holes ||
        index->numbers.low + index->numbers.strict != map->iterate_from || !numbers_subset(&map->codomain, &map->domain) ||
        !numbers_subset(&point->numbers, &map->domain) || !divisions_by_numbers(closed) || !divisions_by_numbers(map->body))
        return verdict;
    int n = index->variable, x = point->variable, letter = 0;
    for (const char *c = "satubvw"; *c && !letter; c++)
        if (*c != n && *c != x && !map_find(*c) && !node_uses_letter(closed, *c) && !node_uses_letter(map->body, *c)) letter = *c;
    if (!letter) return verdict;

    /* Che la regola definisca un'applicazione (18m): i valori stanno nel
     * codominio, e quindi nel dominio. */
    proof_reset();
    universal_count = 0;
    proof_add("\\textbf{Proof.} First the iterates are written as a sequence, then the claim is proved for it.\n\\begin{itemize}\n");
    if (!map_defined(map) || failure) {
        failure = NULL;
        verdict.outcome = NOT_PROVED;
        verdict.reason = "non riesco a dimostrare che la regola dà sempre un valore nel codominio";
        return verdict;
    }

    /* La successione, scritta con put_node(): il primo valore f(x), la
     * regola f(s_n), la tesi. Il testo nasce nella dimostrazione e da lì si
     * copia. */
    Node at = {N_SEQ, 0, letter, 0, NULL, NULL, NULL}, variable = {N_VAR, 0, x, 0, NULL, NULL, NULL}, now = {N_VAR, 0, n, 0, NULL, NULL, NULL};
    at.a = &now;
    const Node *value[3] = {&variable, &at, NULL};
    for (int part = 0; part < 3; part++) {
        size_t start = proof_length;
        shown_name = map->parameter;
        shown_value = value[part];
        put_node(part < 2 ? map->body : closed, 0);
        shown_value = NULL;
        size_t length = proof_length - start;
        if (length >= sizeof shown[part] || failure) return verdict;
        memcpy(shown[part], proof_text + start, length);
        shown[part][length] = 0;
        proof_cut(start);
    }
    snprintf(sequence, sizeof sequence, "%c_{%lld} = %s, %c_{%c + 1} = %s, %c \\ge %lld \\implies %c_{%c} = %s", letter,
             map->iterate_from, shown[0], letter, n, shown[1], n, map->iterate_from, letter, n, shown[2]);
    proof_add("\\item \\emph{The iterates as a sequence.} Fix $%c \\in ", x);
    put_numbers(&point->numbers);
    proof_add("$ and let $%c_{%c} = %c^{%c}(%c)$ for $%c \\ge %lld$. By the hypotheses $%c_{%lld} = %c(%c)$ and $%c_{%c + 1} = "
              "%c(%c_{%c})$: the rule of $%c$ applies to $%c_{%c}$, which is a value of $%c$, because the codomain is part of the "
              "domain. So $%c_{%lld} = %s$ and $%c_{%c + 1} = %s$ for $%c \\ge %lld$, and the claim is $%c_{%c} = %s$.\n\\end{itemize}\n",
              letter, n, map->name, n, x, n, map->iterate_from, letter, map->iterate_from, map->name, x, letter, n, map->name,
              letter, n, map->name, letter, n, map->name, letter, map->iterate_from, shown[0], letter, n, shown[1], n,
              map->iterate_from, letter, n, shown[2]);
    if (proof_length >= sizeof prefix) return verdict;
    memcpy(prefix, proof_text, proof_length + 1);

    /* Il capitolo 26, e la dimostrazione con il suo inizio davanti. */
    map_count = 0;
    Verdict decided = prove_sequence(sequence, n, 1, map->iterate_from);
    if (decided.outcome != PROVED || !decided.proof) return decided;
    const char *heading = "\\textbf{Proof.} ";
    if (strncmp(decided.proof, heading, strlen(heading)) == 0) decided.proof += strlen(heading);
    size_t ahead = strlen(prefix), rest = strlen(decided.proof);
    if (ahead + rest + 1 > PROOF_BYTES) { decided.proof = NULL; decided.outcome = NOT_PROVED; decided.reason = "dimostrazione troppo lunga"; return decided; }
    memmove(proof_text + ahead, decided.proof, rest + 1);
    memcpy(proof_text, prefix, ahead);
    proof_length = ahead + rest;
    decided.proof = proof_text;
    return decided;
}
