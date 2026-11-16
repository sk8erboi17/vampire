/* MODULO engine_intervals: i numeri reali come intervalli con l'errore
 * garantito (capitolo 24).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_intervals.h, e
 * il resto è static. */
#include "engine_intervals.h"
#include "engine_foundations.h"
#include "parser.h"

/* =============================================================================
 * 24. INTERVALLI: NUMERI REALI CON L'ERRORE GARANTITO
 * ============================================================================
 *
 * Quasi tutto il programma fa conti esatti. Ma un numero come log_2 3, la
 * radice quadrata di e, o pi greco diviso 6 non si scrive con una frazione,
 * e per sapere quale di due numeri così viene prima sulla retta non c'è un
 * conto esatto da fare. Qui un numero reale è rappresentato da un
 * intervallo [low, high] che lo contiene di sicuro: se due intervalli non si
 * toccano, l'ordine dei due numeri è certo; se si toccano, la risposta è
 * "non so", mai una risposta sbagliata.
 *
 * Da dove viene la garanzia. I double seguono lo standard IEEE 754: ognuna
 * delle quattro operazioni dà il double più vicino al risultato vero, cioè
 * sbaglia al più di mezza unità sull'ultima cifra. Dopo ogni operazione
 * l'intervallo viene allargato, da tutte e due le parti, di RANGE_EPS volte
 * il suo valore: più dell'errore possibile. Le funzioni (logaritmo,
 * esponenziale, arcotangente, seno, coseno) sono serie di potenze sommate
 * con le stesse operazioni, più un termine che maggiora il resto della
 * serie. math.h non serve, e non si usa.
 *
 * Che cosa non si può fare con gli intervalli: stabilire che due numeri sono
 * uguali. Uno zero esatto va riconosciuto prima, con i conti esatti; qui si
 * arriva solo per confermare che un numero non è zero, e da che parte sta.
 *
 * Un Range con low > high vuol dire "non so" (range_none()): lo danno una
 * divisione per un intervallo che contiene lo zero, un logaritmo di un
 * intervallo che tocca i numeri non positivi, un numero troppo grande. Ogni
 * operazione su un "non so" dà "non so".
 */

#define RANGE_EPS (4 * DBL_EPSILON)  /* allargamento relativo dopo ogni operazione */

/* Ritorna il "non so". */
Range range_none(void) { return (Range){1, -1}; }

/* Ritorna 1 se r è un intervallo vero, 0 se è un "non so". Un estremo
 * infinito o non numerico, sottratto a se stesso, non dà zero. */
int range_known(Range r) { return r.low <= r.high && r.low - r.low == 0 && r.high - r.high == 0; }

/* Ritorna l'intervallo [low, high] allargato quanto basta a coprire
 * l'errore dell'operazione che ha prodotto i due estremi. DBL_MIN copre i
 * numeri così piccoli che l'allargamento relativo sparirebbe. */
Range range_wide(double low, double high) {
    double a = low < 0 ? -low : low, b = high < 0 ? -high : high;
    Range r = {low - a * RANGE_EPS - DBL_MIN, high + b * RANGE_EPS + DBL_MIN};
    return range_known(r) ? r : range_none();
}

/* Ritorna un intervallo che contiene num / den, con den diverso da zero. Le
 * due conversioni in double e la divisione sbagliano ognuna di mezza unità:
 * l'allargamento le copre. */
Range range_ratio(__int128 num, __int128 den) {
    double q = (double)num / (double)den;
    return range_wide(q, q);
}

/* Ritorna -a: cambiare segno è esatto. */
Range range_neg(Range a) { return range_known(a) ? (Range){-a.high, -a.low} : range_none(); }

/* Ritorna a + b. */
Range range_add(Range a, Range b) {
    if (!range_known(a) || !range_known(b)) return range_none();
    return range_wide(a.low + b.low, a.high + b.high);
}

/* Ritorna a * b: il più piccolo e il più grande dei quattro prodotti degli
 * estremi. */
Range range_mul(Range a, Range b) {
    if (!range_known(a) || !range_known(b)) return range_none();
    double p[4] = {a.low * b.low, a.low * b.high, a.high * b.low, a.high * b.high}, low = p[0], high = p[0];
    for (int i = 1; i < 4; i++) {
        if (p[i] < low) low = p[i];
        if (p[i] > high) high = p[i];
    }
    return range_wide(low, high);
}

/* Ritorna 1 / a; "non so" se a contiene lo zero. */
static Range range_inv(Range a) {
    if (!range_known(a) || (a.low <= 0 && a.high >= 0)) return range_none();
    return range_wide(1 / a.high, 1 / a.low);
}

/* Ritorna a - b e a / b. */
Range range_sub(Range a, Range b) { return range_add(a, range_neg(b)); }
Range range_div(Range a, Range b) { return range_mul(a, range_inv(b)); }

/* Ritorna a allargato di margin da tutte e due le parti: per il resto di
 * una serie troncata. */
static Range range_pad(Range a, double margin) {
    return range_known(a) ? range_wide(a.low - margin, a.high + margin) : range_none();
}

/* Ritorna la somma dei primi `terms` termini della serie
 *
 *     y + s y^3 / 3 + s^2 y^5 / 5 + ...        con s = sign (1 oppure -1),
 *
 * che per s = 1 è la tangente iperbolica inversa di y e per s = -1 è
 * l'arcotangente, più il resto. Vale per |y| <= 1/2: il resto dopo n
 * termini è minore di |y|^(2n+1), che con 60 termini è sotto 10^-36. */
static Range range_odd_series(Range y, int sign) {
    Range square = range_mul(y, y), power = y, sum = y;
    for (int j = 1; j < 60; j++) {
        power = range_mul(power, square);
        Range term = range_div(power, range_ratio(2 * j + 1, 1));
        sum = (sign > 0 || j % 2 == 0) ? range_add(sum, term) : range_sub(sum, term);
    }
    return range_pad(sum, 1e-30);
}

/* Ritorna il logaritmo naturale di 2: è 2 atanh(1/3), perché
 * atanh(y) = ln((1 + y) / (1 - y)) / 2. */
Range range_ln2(void) {
    return range_mul(range_ratio(2, 1), range_odd_series(range_ratio(1, 3), 1));
}

/* Ritorna il logaritmo naturale del double v, che è positivo.
 *
 * Si scrive v = m 2^k con m tra radice di 1/2 e radice di 2: dividere e
 * moltiplicare per 2 un double è esatto. Poi ln v = k ln 2 + ln m, e
 * ln m = 2 atanh((m - 1) / (m + 1)), con un argomento minore di 0,18 in
 * valore assoluto, dove la serie converge in fretta. */
static Range range_ln_at(double v) {
    int k = 0;
    if (!(v > 0) || v - v != 0) return range_none();
    for (; v > 1.4142135623730951; k++) v /= 2;
    for (; v < 0.7071067811865476; k--) v *= 2;
    Range m = {v, v}, one = {1, 1};
    Range inner = range_mul(range_ratio(2, 1), range_odd_series(range_div(range_sub(m, one), range_add(m, one)), 1));
    return range_add(inner, range_mul(range_ratio(k, 1), range_ln2()));
}

/* Ritorna il logaritmo naturale di a, "non so" se a non è tutto positivo. Il
 * logaritmo cresce: bastano i due estremi. */
Range range_ln(Range a) {
    if (!range_known(a) || !(a.low > 0)) return range_none();
    Range low = range_ln_at(a.low), high = range_ln_at(a.high);
    return range_known(low) && range_known(high) ? (Range){low.low, high.high} : range_none();
}

/* Ritorna e elevato al double v.
 *
 * Si scrive v = k ln 2 + r con r piccolo: allora e^v = 2^k e^r, ed e^r è la
 * somma di r^j / j!. Con |r| < 1/2 il resto dopo 30 termini è sotto 10^-40.
 * Moltiplicare per 2^k è esatto finché il numero resta nei double. */
Range range_exp_at(double v) {
    if (v - v != 0 || v > 700 || v < -700) return range_none();
    long long k = (long long)(v / 0.6931471805599453 + (v < 0 ? -0.5 : 0.5));
    Range r = range_sub((Range){v, v}, range_mul(range_ratio(k, 1), range_ln2())), term = {1, 1}, sum = {1, 1};
    for (int j = 1; j <= 30; j++) {
        term = range_div(range_mul(term, r), range_ratio(j, 1));
        sum = range_add(sum, term);
    }
    sum = range_pad(sum, 1e-30);
    for (long long i = 0; i < (k < 0 ? -k : k) && range_known(sum); i++) sum = range_wide(k < 0 ? sum.low / 2 : sum.low * 2, k < 0 ? sum.high / 2 : sum.high * 2);
    return sum;
}

/* Ritorna e elevato ad a. L'esponenziale cresce: bastano i due estremi. */
Range range_exp(Range a) {
    if (!range_known(a)) return range_none();
    Range low = range_exp_at(a.low), high = range_exp_at(a.high);
    return range_known(low) && range_known(high) ? (Range){low.low, high.high} : range_none();
}

/* Ritorna la radice quadrata di a, "non so" se a tocca i negativi.
 *
 * Il metodo di Newton dà un double vicino alla radice, ma non dice quanto;
 * lo si allarga e poi si controlla, elevando al quadrato con gli intervalli,
 * che i due estremi stiano davvero uno sotto e uno sopra. */
Range range_sqrt(Range a) {
    if (!range_known(a) || a.low < 0) return range_none();
    double bound[2];
    for (int side = 0; side < 2; side++) {
        double v = side ? a.high : a.low, s = v > 1 ? v : 1;
        if (v == 0) { bound[side] = 0; continue; }
        for (int step = 0; step < 200; step++) s = (s + v / s) / 2;
        Range near = range_wide(s * (1 - 16 * DBL_EPSILON), s * (1 + 16 * DBL_EPSILON));
        Range under = range_mul((Range){near.low, near.low}, (Range){near.low, near.low}), over = range_mul((Range){near.high, near.high}, (Range){near.high, near.high});
        if (!range_known(under) || !range_known(over) || under.high > v || over.low < v) return range_none();
        bound[side] = side ? near.high : near.low;
    }
    return (Range){bound[0], bound[1]};
}

/* Ritorna l'arcotangente di a.
 *
 * La serie dell'arcotangente converge bene solo vicino allo zero. Ci si
 * arriva con la formula di bisezione dell'angolo, atan(t) = 2 atan(u) con
 * u = t / (1 + sqrt(1 + t^2)), ripetuta finché |u| <= 1/2: ogni volta
 * l'angolo si dimezza, e bastano tre giri anche per un t enorme. */
Range range_atan(Range a) {
    Range one = {1, 1};
    int doublings = 0;
    for (; range_known(a) && (a.low < -0.5 || a.high > 0.5) && doublings < 8; doublings++)
        a = range_div(a, range_add(one, range_sqrt(range_add(one, range_mul(a, a)))));
    if (!range_known(a) || a.low < -0.5 || a.high > 0.5) return range_none();
    a = range_odd_series(a, -1);
    for (int i = 0; i < doublings; i++) a = range_add(a, a);
    return a;
}

/* Ritorna pi greco, con la formula di Machin:
 * pi = 16 atan(1/5) - 4 atan(1/239). */
Range range_pi(void) {
    return range_sub(range_mul(range_ratio(16, 1), range_odd_series(range_ratio(1, 5), -1)), range_mul(range_ratio(4, 1), range_odd_series(range_ratio(1, 239), -1)));
}

/* Ritorna arcsin a; "non so" se a non sta tutto in [-1, 1].
 *
 * L'arcoseno è crescente, quindi l'intervallo va dall'arcoseno di un
 * estremo a quello dell'altro. In un estremo t con |t| < 1 l'angolo y =
 * arcsin t, tra -pi/2 e pi/2, ha sin y = t e cos y = sqrt(1 - t^2) > 0,
 * quindi tan y = t / sqrt(1 - t^2) e y è l'arcotangente di quel numero; in
 * t = 1 e t = -1 vale pi/2 e -pi/2. Ogni passo è un'operazione con gli
 * intervalli, che contiene il risultato vero: la scelta tra i due casi
 * guarda se l'estremo è proprio il numero 1, non decide nulla
 * dell'enunciato. */
Range range_asin(Range a) {
    Range ends[2], one = {1, 1}, half_pi = range_div(range_pi(), range_ratio(2, 1));
    if (!range_known(a) || a.low < -1 || a.high > 1) return range_none();
    for (int side = 0; side < 2; side++) {
        Range t = side ? (Range){a.high, a.high} : (Range){a.low, a.low};
        if (t.low == 1 || t.low == -1) ends[side] = t.low > 0 ? half_pi : range_neg(half_pi);
        else ends[side] = range_atan(range_div(t, range_sqrt(range_sub(one, range_mul(t, t)))));
        if (!range_known(ends[side])) return range_none();
    }
    return (Range){ends[0].low, ends[1].high};
}

/* Ritorna pi/2 - b: arccos a = pi/2 - arcsin a, arccot a = pi/2 - arctan a
 * (con l'arcocotangente in (0, pi)). */
Range range_from_half_pi(Range b) { return range_sub(range_div(range_pi(), range_ratio(2, 1)), b); }

/* Mette in *sine e *cosine il seno e il coseno di a.
 *
 * Prima si toglie ad a il multiplo di 2 pi più vicino, che non cambia né
 * l'uno né l'altro; resta un angolo tra -4 e 4, e lì le serie
 *
 *     sin r = r - r^3/3! + r^5/5! - ...      cos r = 1 - r^2/2! + r^4/4! - ...
 *
 * sommate fino al grado 60 hanno un resto sotto 10^-45 (4^61 / 61!). */
void range_sin_cos(Range a, Range *sine, Range *cosine) {
    *sine = *cosine = range_none();
    if (!range_known(a) || a.low < -1e9 || a.high > 1e9) return;
    Range turn = range_mul(range_ratio(2, 1), range_pi());
    double middle = (a.low + a.high) / 2 / 6.283185307179586;
    Range r = range_sub(a, range_mul(range_ratio((long long)(middle + (middle < 0 ? -0.5 : 0.5)), 1), turn));
    if (!range_known(r) || r.low < -4 || r.high > 4) return;
    Range term = {1, 1}, even = {1, 1}, odd = {0, 0};
    for (int j = 1; j <= 60; j++) {
        /* term è r^j / j!; i gradi dispari vanno al seno, i pari al coseno,
         * con i segni alterni: + per j = 1, 4, 5, 8, 9, ... */
        term = range_div(range_mul(term, r), range_ratio(j, 1));
        Range signed_term = (j % 4 == 2 || j % 4 == 3) ? range_neg(term) : term;
        if (j % 2) odd = range_add(odd, signed_term); else even = range_add(even, signed_term);
    }
    *sine = range_pad(odd, 1e-30);
    *cosine = range_pad(even, 1e-30);
}

/* Se il segno di r è certo lo mette in *side (1 o -1) e ritorna 1; ritorna
 * 0 se r contiene lo zero o è un "non so". */
int range_side(Range r, int *side) {
    if (!range_known(r) || (r.low <= 0 && r.high >= 0)) return 0;
    *side = r.low > 0 ? 1 : -1;
    return 1;
}

/* Ritorna a elevato all'intero e, con moltiplicazioni ripetute. */
Range range_power(Range a, long long e) {
    Range result = {1, 1};
    for (long long i = 0; i < (e < 0 ? -e : e) && range_known(result); i++) result = range_mul(result, a);
    return e < 0 ? range_inv(result) : result;
}

/* Ritorna un intervallo che contiene il valore dell'espressione node quando
 * la variabile name sta in x; "non so" se non riesce a calcolarlo. Mette 1
 * in *undefined, che chi chiama ha messo a 0, quando è certo che lì
 * l'espressione non ha un valore: la radice o il logaritmo di un numero
 * sicuramente negativo. La lettera e, quando non è la variabile, è il numero
 * di Nepero.
 *
 * Serve in due posti: a ricontrollare con i numeri una riga della tabella
 * dei segni, dove conta il segno certo di una differenza, e a tracciare le
 * curve di un grafico, dove basta il punto medio. Somme, prodotti estesi e
 * applicazioni dichiarate non li calcola. */
Range node_range(const Node *node, int name, Range x, int *undefined) {
    Range a, b, sine, cosine;
    switch (node->kind) {
    case N_NUM: return range_ratio(node->value, 1);
    case N_VAR:
        if (node->name == name) return x;
        if (node->name == VAR_PI) return range_pi();
        return node->name == 'e' ? range_exp_at(1) : range_none();
    case N_NEG: return range_neg(node_range(node->a, name, x, undefined));
    case N_ADD: return range_add(node_range(node->a, name, x, undefined), node_range(node->b, name, x, undefined));
    case N_SUB: return range_sub(node_range(node->a, name, x, undefined), node_range(node->b, name, x, undefined));
    case N_MUL: return range_mul(node_range(node->a, name, x, undefined), node_range(node->b, name, x, undefined));
    case N_DIV: return range_div(node_range(node->a, name, x, undefined), node_range(node->b, name, x, undefined));
    case N_POW: {
        /* Un esponente intero scritto come numero: moltiplicazioni. Ogni
         * altro esponente chiede una base positiva: a^b = e^(b ln a). */
        const Node *exponent = node->b->kind == N_NEG ? node->b->a : node->b;
        a = node_range(node->a, name, x, undefined);
        if (exponent->kind == N_NUM && exponent->value <= MAX_UNI) return range_power(a, node->b->kind == N_NEG ? -exponent->value : exponent->value);
        if (range_known(a) && a.high < 0) *undefined = 1;
        return range_exp(range_mul(node_range(node->b, name, x, undefined), range_ln(a)));
    }
    case N_CALL:
        a = node_range(node->a, name, x, undefined);
        if (!range_known(a)) return a;
        switch (node->op) {
        case FN_ABS:
            if (a.low >= 0 || a.high <= 0) return a.low >= 0 ? a : range_neg(a);
            return (Range){0, -a.low > a.high ? -a.low : a.high};
        case FN_ROOT:
            /* La radice quadrata; le altre, per un radicando positivo, come
             * potenze con esponente 1/n; quelle di indice dispari di un
             * radicando negativo come -(-a)^{1/n} (11o). */
            if (node->b->kind != N_NUM || node->b->value < 2) return range_none();
            if (a.high < 0 && node->b->value % 2 == 0) *undefined = 1;
            if (node->b->value == 2) return range_sqrt(a);
            if (a.high < 0 && node->b->value % 2) return range_neg(range_exp(range_div(range_ln(range_neg(a)), range_ratio(node->b->value, 1))));
            return range_exp(range_div(range_ln(a), range_ratio(node->b->value, 1)));
        case FN_LN:
        case FN_LOG:
            if (a.high <= 0) *undefined = 1;
            a = range_ln(a);
            if (node->op == FN_LN) return a;
            if (!node->b) return range_none();
            b = node_range(node->b, name, x, undefined);
            return range_div(a, range_ln(b));
        case FN_SIN: case FN_COS: case FN_TAN: case FN_COT:
            range_sin_cos(a, &sine, &cosine);
            if (node->op == FN_SIN || node->op == FN_COS) return node->op == FN_SIN ? sine : cosine;
            return node->op == FN_TAN ? range_div(sine, cosine) : range_div(cosine, sine);
        case FN_ARCTAN: return range_atan(a);
        case FN_ARCCOT: return range_from_half_pi(range_atan(a));
        case FN_ARCSIN: case FN_ARCCOS:
            /* Fuori da [-1, 1] l'argomento non ha arcoseno. */
            if (a.low > 1 || a.high < -1) *undefined = 1;
            return node->op == FN_ARCSIN ? range_asin(a) : range_from_half_pi(range_asin(a));
        default: return range_none();
        }
    default:
        return range_none();
    }
}

/* Ritorna un intervallo che contiene il numero p, un polinomio negli atomi
 * che sono numeri: un primo elevato a un razionale, il logaritmo di un
 * primo, i numeri e e pi. "Non so" se p contiene altro. */
Range poly_range(Poly p) {
    Range sum = {0, 0};
    for (int t = 0; t < p.count; t++) {
        const Term *term = &p.term[t];
        if (term->coef.im.num != 0) return range_none();
        Range product = range_ratio(term->coef.re.num, term->coef.re.den);
        for (int f = 0; f < term->mono.count; f++) {
            const Atom *atom = &atoms[term->mono.factor[f].atom];
            Frac e = term->mono.factor[f].exp;
            Range base;
            if (atom->kind == ATOM_VAR && atom->id == 'e') base = range_exp_at(1);
            else if (atom->kind == ATOM_VAR && atom->id == VAR_PI) base = range_pi();
            else if (atom->base != BASE_PRIME || atom->exponent.count != 0) return range_none();
            else if (atom->kind == ATOM_POW) base = range_ratio(atom->id, 1);
            else if (atom->kind == ATOM_LN) base = range_ln(range_ratio(atom->id, 1));
            else return range_none();

            /* base^e: con e intero sono moltiplicazioni, altrimenti
             * e^(e ln base), per una base positiva. */
            product = range_mul(product, e.den == 1 ? range_power(base, e.num) : range_exp(range_mul(range_ratio(e.num, e.den), range_ln(base))));
        }
        sum = range_add(sum, product);
    }
    return sum;
}
