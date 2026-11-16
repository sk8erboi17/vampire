/* MODULO engine_induction: induzione su somme e prodotti: caso base, passo,
 * verdetto (capitolo 13).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_induction.h, e
 * il resto è static. */
#include "engine_induction.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_derivatives.h"

/* =============================================================================
 * 13. INDUZIONE: CASO BASE, PASSO, VERDETTO
 * ============================================================================
 *
 * Sia D(n) = L(n) - R(n) la differenza dei due membri. L'enunciato dice che
 * D(n) = 0 per ogni n >= n0. Il principio di induzione chiede due cose:
 *
 *   13a. Caso base: D(n0) = 0. Con n = n0 ogni somma e prodotto si svolge e
 *        D(n0) è un'espressione senza n: deve annullarsi.
 *
 *   13b. Passo: per ogni n >= n0, da D(n) = 0 segue D(n+1) = 0.
 *        Si scrivono D(n) e D(n+1) con gli stessi atomi. L'ipotesi induttiva
 *        D(n) = 0 è un'equazione tra gli atomi: se un atomo X (di solito la
 *        somma dell'enunciato) vi compare al primo grado, numeratore
 *        A X + B = 0, se ne ricava X = -B/A. Sostituendo nel numeratore di
 *        D(n+1), che è un polinomio C0 + C1 X + ... + Cd X^d, e moltiplicando
 *        per A^d si ottiene
 *
 *            C0 A^d + C1 (-B) A^{d-1} + ... + Cd (-B)^d
 *
 *        che non contiene più X: se è il polinomio nullo il passo è
 *        dimostrato. È ciò che si fa a mano: "per ipotesi induttiva la somma
 *        fino a n vale R(n), quindi la somma fino a n+1 vale R(n) + f(n+1), e
 *        resta da controllare che sia R(n+1)".
 *
 * Quando l'ipotesi si può usare. Ricavare X = -B/A richiede A diverso da zero
 * per ogni n >= n0. Senza questa cautela si "dimostrerebbero" enunciati falsi:
 * in (n-1) S(n) = (n-1) g(n) il caso base n = 1 dice 0 = 0 qualunque sia g.
 * Il programma accetta due situazioni in cui la condizione è garantita:
 *
 *   - A è proporzionale al denominatore di D: allora X compare in D con un
 *     coefficiente costante (il caso "somma = formula"), e A non si annulla
 *     dove l'enunciato è definito;
 *   - A non dipende da n: dipende solo dai parametri, e un'uguaglianza tra
 *     funzioni razionali dei parametri, vera dove A non è zero, è vera ovunque
 *     sia definita.
 *
 * Negli altri casi servirebbe dimostrare che A non ha zeri interi: il
 * programma non lo sa fare e risponde NON DIMOSTRATO.
 *
 * Se l'induzione non riesce si cerca un controesempio: D valutata in pochi n
 * successivi. Un valore che è un numero diverso da zero prova che l'enunciato
 * è falso.
 *
 * Se l'induzione riesce, il verdetto non è ancora dato:
 *
 *   13c. si decide se i due membri sono definiti per ogni n, con un valore
 *        fisso dei parametri;
 *   13d. oppure, se un valore fisso non c'è, per tutti i valori dei parametri
 *        abbastanza grandi;
 *   13e. la dimostrazione viene ricontrollata con i numeri (verify_instances());
 *   13f. si scrive la dimostrazione, con i suoi passaggi;
 *   13g. ogni formula scritta viene riletta e ricontrollata;
 *   13h. si scrive il certificato dell'induzione e lo si dà al verificatore
 *        indipendente, checker.c.
 */

/* Il testo della dimostrazione dell'enunciato in corso: LaTeX, in inglese come
 * gli altri testi destinati a un documento. proof_reset() lo svuota,
 * proof_add() vi aggiunge un pezzo con la sintassi di printf. Un testo più
 * lungo di PROOF_BYTES viene rifiutato, salvo i modelli che crescono sullo heap. */
static char proof_initial[PROOF_BYTES];
char *proof_text = proof_initial;
size_t proof_length, proof_capacity = PROOF_BYTES;
int proof_growable, proof_broken;

/* Allarga un testo sullo heap entro il budget richiesto. Il deposito
 * iniziale resta statico per i domini che usano testi di lunghezza nota;
 * nessun puntatore al testo va conservato durante una crescita. */
static int text_reserve(char **text, size_t *capacity, char *initial, size_t need) {
    if (need <= *capacity) return 1;
    size_t cap = *capacity;
    while (cap < need) {
        if (cap > (size_t)-1 / 2) { cap = need; break; }
        cap *= 2;
    }
    if (cap > model_memory_limit) return 0;
    char *p = *text == initial ? malloc(cap) : realloc(*text, cap);
    if (!p) return 0;
    if (*text == initial) memcpy(p, initial, *capacity);
    *text = p; *capacity = cap;
    return 1;
}

/* Quanti passi di una dimostrazione scritta non hanno superato il controllo
 * indipendente, dall'avvio del programma. Le dimostrazioni sugli insiemi e
 * quelle con quantificatori ricontrollano ogni fatto che stanno per scrivere
 * con un metodo diverso da quello che lo ha ricavato (16h e 16i, e i
 * controlli del capitolo 18); quelle per induzione rileggono ogni formula
 * scritta e la ricalcolano con i numeri (13g). Se un passo non regge, la
 * dimostrazione viene abbandonata e il contatore sale. Sale anche quando il
 * verificatore indipendente respinge un certificato: di un'induzione (13h),
 * di un enunciato sugli insiemi, di uno su insiemi qualsiasi (28f).
 * Deve restare a zero: un valore diverso vuol dire che una regola ha
 * sbagliato, e i test lo controllano. */
int unjustified_steps;

/* Svuota il documento e restituisce il deposito iniziale; i risultati
 * della chiamata precedente, come per l'arena, non sono piu validi. */
void proof_reset(void) {
    if (proof_text != proof_initial) free(proof_text);
    proof_text = proof_initial; proof_capacity = PROOF_BYTES;
    proof_length = 0; proof_growable = proof_broken = 0;
    proof_text[0] = 0;
}

/* Aggiunge LaTeX. Solo la stampa di un modello abilita la crescita: gli
 * altri domini conservano i propri controlli di lunghezza. Un testo che
 * non entra resta marcato come incompleto, mai consegnato come modello. */
void proof_add(const char *format, ...) {
    if (proof_broken) return;
    va_list arguments;
    va_start(arguments, format);
    va_list retry; va_copy(retry, arguments);
    int written = vsnprintf(proof_text + proof_length, proof_capacity - proof_length, format, arguments);
    if (written < 0 || (size_t)written > (size_t)-1 - proof_length - 1) proof_broken = 1;
    else {
        size_t need = proof_length + (size_t)written + 1;
        if (need > proof_capacity) {
            if (!proof_growable || !text_reserve(&proof_text, &proof_capacity, proof_initial, need)) {
                /* I vecchi chiamanti riconoscono il troncamento dalla lunghezza. */
                proof_length = proof_capacity - 1; proof_broken = 1;
            } else vsnprintf(proof_text + proof_length, proof_capacity - proof_length, format, retry);
        }
        if (!proof_broken) proof_length += (size_t)written;
    }
    va_end(retry);
    va_end(arguments);
}

/* Passo induttivo (13b): d è D(n), d1 è D(n+1), scritte con gli stessi atomi.
 * Ritorna 1 se da D(n) = 0 segue D(n+1) = 0, e allora mette in *used l'atomo
 * ricavato dall'ipotesi, oppure -1 se l'ipotesi non è servita. */
static int step_holds(Rat d, Rat d1, int *used) {
    /* D(n+1) è già zero: non serve nemmeno l'ipotesi. */
    *used = -1;
    if (poly_vanishes(d1.num)) return 1;

    /* Si prova a ricavare dall'ipotesi ogni somma o prodotto, uno alla volta. */
    for (int x = 0; x < atom_count && !failure; x++) {
        if (atoms[x].kind != ATOM_BIGOP) continue;

        /* Ipotesi: A x + B = 0, con A che non si annulla. */
        Poly hypothesis[2], part[MAX_DEGREE + 1];
        if (poly_split(d.num, x, hypothesis, 1) != 1) continue;
        Poly a = hypothesis[1], b = hypothesis[0];
        if (!poly_proportional(a, d.den) && poly_depends_on_n(a)) continue;

        /* Tesi: C0 + C1 x + ... + Cd x^d = 0. */
        int degree = poly_split(d1.num, x, part, MAX_DEGREE);
        if (degree < 0) continue;

        /* Sostituzione x = -B/A, moltiplicata per A^d. Le potenze di -B e di A
         * si accumulano mentre j cresce e d - j decresce. */
        Poly minus_b = poly_add(poly_const(num_int(0)), b, 1);
        Poly b_power = poly_const(num_int(1));
        Poly sum = poly_const(num_int(0));
        for (int j = 0; j <= degree; j++) {
            Poly piece = poly_mul(part[j], b_power);
            for (int k = j; k < degree; k++) piece = poly_mul(piece, a);
            sum = poly_add(sum, piece, 0);
            b_power = poly_mul(b_power, minus_b);
        }
        if (!failure && poly_vanishes(sum)) { *used = x; return 1; }
    }
    return 0;
}

/* 13c. DEFINITO PER OGNI n
 *
 * L'induzione è algebra sulle lettere: prova che i due membri sono uguali
 * "dove sono definiti". Perché il verdetto "per ogni n >= n0" sia vero serve
 * anche che lo siano per ogni n >= n0. In
 *
 *     (n - 50) / (n - 50) = 1
 *
 * l'algebra non trova nulla da ridire, e i primi n nemmeno, ma per n = 50 il
 * membro sinistro non esiste. Lo stesso vale per le divisioni che fa il conto
 * stesso: scrivere un prodotto fino a n - 1 come "prodotto fino a n diviso
 * l'ultimo fattore" (vedi eval_bigop()) è lecito solo dove quel fattore non è
 * zero.
 *
 * Le condizioni di esistenza (capitolo 7) vengono raccolte calcolando D(n) e
 * D(n+1) con n lettera e i parametri legati a numeri: sono polinomi negli
 * atomi, e condition_holds() decide ciascuna per ogni intero n >= n0. Bastano
 * queste due valutazioni: il caso n = n0 è già stato calcolato con i numeri,
 * D(n+1) contiene tutto ciò che compare passando da n a n + 1 (i due membri
 * in n + 1 e i termini nuovi di ogni somma), e D(n) le divisioni fatte per
 * scrivere l'ipotesi.
 *
 * La decisione ha tre risposte: vale (1), non vale (0, con un n in cui
 * fallisce), non so (-1). Le regole, nell'ordine in cui si provano (nel file
 * stanno nell'ordine in cui una ha bisogno dell'altra):
 *
 *   13c-1. Un seno o un coseno, eventualmente per un fattore positivo: il
 *          segno viene dal quadrante in cui cade l'angolo (trig_sign()).
 *   13c-2. Si raccoglie il monomio comune ai termini. I suoi atomi devono
 *          essere mai nulli (per "diverso da zero") o positivi (per i segni):
 *          n da 1 in su, le potenze di un primo, i prodotti di fattori
 *          positivi, le potenze di una base che a sua volta lo è.
 *   13c-3. Ciò che resta è un polinomio in una sola quantità che cresce con
 *          n, la "variabile principale": n stessa, o una potenza come 2^n.
 *          Il segno si decide con il limite di Cauchy (sign_holds()).
 *   13c-4. Ciò che resta contiene la variabile principale e radici di numeri
 *          primi, come la radice di 2: gli zeri si trovano con le radici
 *          razionali (zero_free()).
 *   13c-5. Altrimenti si guarda se il segno è evidente: coefficienti tutti
 *          dello stesso segno e fattori non negativi (evident_sign()).
 *   13c-6. Un'espressione che non decresce ed è positiva per n = n0, o che
 *          non cresce ed è negativa (monotone_sign()).
 *   13c-7. Un'espressione in n e in potenze come 2^n e 3^n, che crescono a
 *          velocità diverse: il segno per differenze (difference_rule()).
 *   13c-8. Per "diverso da zero", con seni e coseni: esponenziali complessi
 *          che non possono cancellarsi (exponentials_never_cancel()).
 *
 * Ogni regola conclude solo ciò che è certo. In particolare nessuna prende
 * per "diverso da zero" un'espressione solo perché non è il polinomio nullo:
 * tra gli atomi ci sono identità che la forma canonica non vede. Quando
 * nessuna regola decide, la risposta è "non so", e il verdetto sarà
 * NON DIMOSTRATO: di n! - 5 il programma non sa dire che non si annulla. */

/* Ritorna il segno, -1, 0 o 1, di c[0] + c[1] x + ... + c[degree] x^degree
 * nell'intero x, con lo schema di Horner. Se i numeri escono dall'aritmetica
 * esatta mette 0 in *known, che chi chiama ha messo a 1. */
static int univariate_sign(const long long *c, int degree, long long x, int *known) {
    __int128 value = 0;
    for (int i = degree; i >= 0; i--)
        if (__builtin_mul_overflow(value, (__int128)x, &value) || __builtin_add_overflow(value, (__int128)c[i], &value)) {
            *known = 0;
            return 0;
        }
    return (value > 0) - (value < 0);
}

/* Ritorna +1 se il monomio, per n >= base, è positivo e non decresce al
 * crescere di n; -1 se è positivo e non cresce; 0 se non si sa, o se non ha
 * fattori. I mattoni sono n (da 1 in su) e le potenze p^M di un primo, che
 * seguono l'andamento dell'esponente M perché p > 1; un esponente negativo
 * rovescia l'andamento. Un prodotto di quantità positive che vanno tutte
 * nello stesso verso va in quel verso. */
static int mono_trend(const Mono *m, long long base) {
    int trend = 0;
    for (int i = 0; i < m->count; i++) {
        const Atom *a = &atoms[m->factor[i].atom];
        int own;
        if (a->kind == ATOM_VAR && a->id == induction_var && base >= 1) own = 1;
        else if (a->kind == ATOM_POW && a->base == BASE_PRIME) own = mono_trend(&a->exponent, base);
        else return 0;
        if (m->factor[i].exp.num < 0) own = -own;
        if (own == 0 || (trend && own != trend)) return 0;
        trend = own;
    }
    return trend;
}

/* Mette in *value il valore del monomio per n = base e ritorna 1, se è un
 * razionale che si calcola con potenze intere di n e di numeri primi;
 * altrimenti ritorna 0. Numeri troppo grandi lasciano l'errore in `failure`. */
static int mono_at(const Mono *m, long long base, Frac *value) {
    *value = frac_int(1);
    for (int i = 0; i < m->count && !failure; i++) {
        const Atom *a = &atoms[m->factor[i].atom];
        Frac e = m->factor[i].exp, v, power;
        if (e.den != 1 || e.num > 62 || e.num < -62) return 0;
        if (a->kind == ATOM_VAR && a->id == induction_var) {
            v = frac_int(base);
        } else if (a->kind == ATOM_POW && a->base == BASE_PRIME) {
            if (!mono_at(&a->exponent, base, &power) || power.den != 1 || power.num > 62 || power.num < -62) return 0;
            v = frac_int(1);
            for (long long k = llabs(power.num); k > 0 && !failure; k--)
                v = power.num > 0 ? frac_mul(v, frac_int(a->id)) : frac_div(v, frac_int(a->id));
        } else {
            return 0;
        }
        if (v.num == 0 && e.num < 0) return 0;
        for (long long k = llabs(e.num); k > 0 && !failure; k--) *value = e.num > 0 ? frac_mul(*value, v) : frac_div(*value, v);
    }
    return !failure;
}

/* LA VARIABILE PRINCIPALE
 *
 * Le regole 13c-3 e 13c-4 decidono un polinomio in una sola quantità che
 * cresce con n prendendo valori interi: n stessa, oppure una potenza come
 * 2^n. Di 2 A^2 - 3 A + 1 con A = 2^n si trovano le radici intere in A, e poi
 * si guarda se 2^n le raggiunge. Così la stessa regola che per n - 50 trova
 * n = 50 trova per 2^n - 4096 il valore n = 12. */

/* Ritorna l'atomo che fa da variabile principale di q per n >= base: l'unico
 * atomo di q che dipende da n, se è n oppure una potenza p^M di un primo con
 * M intero e crescente. Se q non dipende da n ritorna n. Ritorna -1 se gli
 * atomi che dipendono da n sono più d'uno, o di un altro tipo. */
static int main_atom(Poly q, long long base) {
    int found = -1;
    for (int i = 0; i < q.count; i++)
        for (int f = 0; f < q.term[i].mono.count; f++) {
            int atom = q.term[i].mono.factor[f].atom;
            if (!atoms[atom].depends_on_n) continue;
            if (found >= 0 && atom != found) return -1;
            found = atom;
        }
    if (found < 0) return atom_var(induction_var);
    const Atom *a = &atoms[found];
    if (a->kind == ATOM_VAR) return found;
    int power = a->kind == ATOM_POW && a->base == BASE_PRIME && mono_is_integer(&a->exponent);
    return power && mono_trend(&a->exponent, base) == 1 ? found : -1;
}

/* Mette in *value il valore intero della variabile principale `atom` per
 * n = at, e ritorna 1; ritorna 0 se non è un intero che si sa calcolare. */
static int main_at(int atom, long long at, long long *value) {
    Mono single = mono_atom(atom, frac_int(1));
    Frac v;
    if (!mono_at(&single, at, &v) || v.den != 1) return 0;
    *value = v.num;
    return 1;
}

/* 13c-3. Decide se il polinomio a coefficienti interi c[0..degree] nella
 * variabile principale `atom`, con c[degree] diverso da zero, è positivo
 * (strict) o non negativo per ogni intero n >= base. Ritorna 1, oppure 0 con
 * il primo n in cui fallisce in *where, oppure -1 se i valori da provare sono
 * troppi o troppo grandi.
 *
 * Limite di Cauchy: ogni radice reale r del polinomio soddisfa
 * |r| < 1 + M, dove M è il più grande |c[i]| / |c[degree]| con i < degree.
 * Infatti se |x| >= 1 + M la somma dei termini di grado più basso vale al più
 * M |c[degree]| (|x|^degree - 1) / (|x| - 1) <= |c[degree]| (|x|^degree - 1),
 * meno del termine di grado massimo: il polinomio non può annullarsi.
 *
 * Oltre il limite il segno quindi non cambia più. La variabile principale
 * cresce con n: si provano i suoi valori uno dopo l'altro finché non
 * superano il limite. Se nessuno fallisce, nemmeno l'ultimo, il segno resta
 * quello buono per sempre. */
static int sign_holds(const long long *c, int degree, int strict, int atom, long long base, long long *where) {
    long long largest = 0, x;
    for (int i = 0; i < degree; i++)
        if (llabs(c[i]) > largest) largest = llabs(c[i]);
    long long bound = largest / llabs(c[degree]) + 2;
    for (long long at = base; at - base <= MAX_SCAN; at++) {
        int known = 1;
        if (!main_at(atom, at, &x)) return -1;
        int sign = univariate_sign(c, degree, x, &known);
        if (!known) return -1;
        if (sign < 0 || (strict && sign == 0)) { *where = at; return 0; }
        if (degree == 0 || x >= bound) return 1;
    }
    return -1;
}

/* 13c-4. Decide se q è diverso da zero per ogni intero n >= base, quando la
 * variabile principale `atom` vi compare solo con potenze intere e gli altri
 * atomi sono radici di numeri primi. Ritorna 1, oppure 0 con il più piccolo n in cui
 * si annulla in *where, oppure -1 se q non ha questa forma o un conto non
 * riesce.
 *
 * Detta A la variabile principale, q è una somma c_1(A) m_1 + ... +
 * c_r(A) m_r, dove gli m_j sono monomi distinti negli atomi costanti e i c_j
 * polinomi a coefficienti razionali. Se gli m_j sono linearmente
 * indipendenti sui razionali, q si annulla dove A vale r solo se tutti i c_j
 * si annullano in r. I valori interi di A in cui q si annulla sono allora
 * tra le radici intere di uno qualunque dei c_j, che il teorema delle radici
 * razionali elenca tutte (rational_roots()). Di ognuna si guarda se A la
 * raggiunge per qualche n >= base, e se annulla tutto q.
 *
 * L'indipendenza va garantita, non supposta: qui un legame nascosto tra gli
 * m_j farebbe perdere uno zero, cioè accettare una divisione per zero. Per
 * questo gli atomi costanti ammessi sono solo le radici di numeri primi,
 * come la radice di 2 e la radice cubica di 5: i loro prodotti distinti sono
 * linearmente indipendenti sui razionali (teorema di Besicovitch; il caso
 * più noto è che 1, radice di 2, radice di 3 e radice di 6 lo sono). Altri
 * atomi costanti soddisfano identità: arctan(1/2) + arctan(1/3) = pi/4, e
 * 2 cos(pi/3) = 1 tra le potenze di e^{i pi}. */
static int zero_free(Poly q, int atom, long long base, long long *where) {
    const long long cap = 1000000000;
    int answer = 1;
    Poly part[MAX_UNIVARIATE + 1];
    Frac coefficient[MAX_UNIVARIATE + 1], root[MAX_UNIVARIATE + 1];
    long long c[MAX_UNIVARIATE + 1];

    /* q = part[0] + part[1] A + ... + part[degree] A^degree. */
    int degree = poly_split(q, atom, part, MAX_UNIVARIATE);
    if (degree < 0) return -1;
    for (int j = 0; j <= degree; j++)
        for (int i = 0; i < part[j].count; i++)
            for (int f = 0; f < part[j].term[i].mono.count; f++) {
                const Atom *a = &atoms[part[j].term[i].mono.factor[f].atom];
                if (a->kind != ATOM_POW || a->base != BASE_PRIME || a->exponent.count != 0) return -1;
            }

    /* Il polinomio c(A) che moltiplica uno dei monomi costanti: quello del
     * primo termine della parte di grado massimo. Di un coefficiente
     * complesso si guarda la parte reale, o quella immaginaria se la reale
     * manca: c(r) = 0 le annulla entrambe. */
    const Term *chosen = &part[degree].term[0];
    int imaginary = chosen->coef.re.num == 0;
    __int128 scale = 1;
    for (int j = 0; j <= degree; j++) {
        coefficient[j] = frac_int(0);
        for (int i = 0; i < part[j].count; i++)
            if (mono_cmp(&part[j].term[i].mono, &chosen->mono) == 0)
                coefficient[j] = imaginary ? part[j].term[i].coef.im : part[j].term[i].coef.re;
        scale = scale / gcd128(scale, coefficient[j].den) * coefficient[j].den;
        if (scale > cap) return -1;
    }
    for (int j = 0; j <= degree; j++) {
        __int128 value = (__int128)coefficient[j].num * (scale / coefficient[j].den);
        if (value > cap || value < -cap) return -1;
        c[j] = (long long)value;
    }

    /* Le radici intere di c(A). */
    int roots = degree >= 1 ? rational_roots(c, degree, root) : 0;
    if (roots < 0) return -1;
    for (int k = 0; k < roots; k++) {
        if (root[k].den != 1) continue;

        /* A cresce: raggiunge la radice per un solo n, o la salta. */
        long long at = base, x = 0;
        while (at - base <= MAX_SCAN && main_at(atom, at, &x) && x < root[k].num) at++;
        if (failure || at - base > MAX_SCAN) return -1;
        if (x != root[k].num) continue;

        /* La radice annulla tutto q? Schema di Horner sui polinomi. */
        Poly value = part[degree], r = poly_const(num_int(root[k].num));
        for (int j = degree - 1; j >= 0; j--) value = poly_add(poly_mul(value, r), part[j], 0);
        if (failure) return -1;
        if (poly_vanishes(value) && (answer == 1 || at < *where)) { answer = 0; *where = at; }
    }
    return answer;
}

int condition_holds(Requirement kind, Poly p, long long base, long long *where);

/* Ritorna 1 se l'atomo è certamente positivo per ogni n >= base: n da 1 in
 * su, pi greco, le potenze di un primo, i prodotti di fattori positivi, le
 * potenze di una base positiva (una radice di n + 1 è l'atomo "n + 1" elevato
 * a 1/2), il logaritmo di un primo, l'arcotangente di un argomento positivo.
 * Zero vuol dire "non si sa". */
int atom_is_positive(int atom, long long base) {
    const Atom *a = &atoms[atom];
    long long where;
    if (a->kind == ATOM_VAR) return a->id == VAR_PI || (a->id == induction_var && base >= 1);
    if (a->kind == ATOM_BIGOP) return a->positive;
    if (a->kind == ATOM_ATAN) {
        Rat u = atan_args[a->id];
        return condition_holds(ALWAYS_POSITIVE, poly_mul(u.num, u.den), base, &where) == 1;
    }
    if (a->kind == ATOM_LN) return a->base == BASE_PRIME;
    if (a->kind != ATOM_POW || a->base == BASE_EI) return 0;
    if (a->base == BASE_PRIME) return 1;
    if (a->base == BASE_ATOM) return atom_is_positive((int)a->id, base);
    return condition_holds(ALWAYS_POSITIVE, base_polys[a->id], base, &where) == 1;
}

/* Decide se l'atomo è diverso da zero per ogni n >= base: 1, 0 (con lo zero
 * in *where) o -1. Una potenza si annulla solo se si annulla la base; e^{i M}
 * mai; un'arcotangente solo se si annulla l'argomento. */
static int atom_never_zero(int atom, long long base, long long *where) {
    const Atom *a = &atoms[atom];
    if (a->kind == ATOM_VAR && a->id == induction_var) {
        *where = 0;
        return base >= 1;
    }
    if (a->kind == ATOM_VAR) return a->id == VAR_PI ? 1 : -1;
    if (a->kind == ATOM_BIGOP) return a->positive ? 1 : -1;
    if (a->kind == ATOM_ATAN) return condition_holds(NEVER_ZERO, atan_args[a->id].num, base, where);
    if (a->kind == ATOM_REC) return -1;
    if (a->base == BASE_PRIME || (a->kind == ATOM_POW && a->base == BASE_EI)) return 1;
    Poly inner = a->base == BASE_ATOM ? rat_atom((int)a->id).num : base_polys[a->id];
    if (a->kind == ATOM_POW) return condition_holds(NEVER_ZERO, inner, base, where);

    /* Un logaritmo ln|u| vale zero solo dove u = 1 oppure u = -1. */
    int below = condition_holds(NEVER_ZERO, poly_add(inner, poly_const(num_int(1)), 1), base, where);
    return below == 1 ? condition_holds(NEVER_ZERO, poly_add(inner, poly_const(num_int(1)), 0), base, where) : below;
}

/* 13c-5. Ritorna 1 se q è evidentemente positivo per ogni n >= base, -1 se
 * evidentemente negativo, 0 se non si vede. Evidente vuol dire: coefficienti
 * tutti dello stesso segno; ogni fattore positivo, oppure non negativo con
 * esponente positivo, oppure potenza pari di un atomo reale; e almeno un
 * termine fatto solo di fattori positivi, che tiene la somma lontana da
 * zero. */
static int evident_sign(Poly q, long long base) {
    int sign = 0, strict = 0;
    for (int i = 0; i < q.count; i++) {
        const Term *t = &q.term[i];
        int positive = 1, own = t->coef.re.num > 0 ? 1 : -1;
        if (t->coef.im.num != 0 || (sign && own != sign)) return 0;
        sign = own;
        for (int f = 0; f < t->mono.count; f++) {
            const Factor *factor = &t->mono.factor[f];
            if (atom_is_positive(factor->atom, base)) continue;
            int even = factor->exp.den == 1 && factor->exp.num % 2 == 0;
            if (factor->exp.num < 0 || !(atom_is_nonnegative(factor->atom) || (even && atom_is_real(factor->atom)))) return 0;
            positive = 0;
        }
        if (positive) strict = 1;
    }
    return strict ? sign : 0;
}

/* 13c-6. Ritorna 1 se q è positivo per ogni n >= base, -1 se è negativo, 0
 * se questa regola non lo stabilisce.
 *
 * Se ogni termine che dipende da n non decresce al crescere di n (un
 * monomio che non decresce con coefficiente positivo, o uno che non cresce
 * con coefficiente negativo), q non decresce: se è positivo per n = base lo
 * è per sempre. Allo stesso modo, se nessun termine cresce e q è negativo in
 * base, resta negativo. Così 2^{2^n} - 1 è positivo da n = 1 in poi, mentre
 * di 2^n - 4096, che in n = 1 è negativo e cresce, non si conclude nulla (e
 * infatti si annulla per n = 12). */
static int monotone_sign(Poly q, long long base) {
    int direction = 0;
    Frac total = frac_int(0), v;
    for (int i = 0; i < q.count; i++) {
        const Term *t = &q.term[i];
        if (t->coef.im.num != 0 || !mono_at(&t->mono, base, &v)) return 0;
        total = frac_add(total, frac_mul(t->coef.re, v));
        if (t->mono.count == 0) continue;
        int own = mono_trend(&t->mono, base);
        if (t->coef.re.num < 0) own = -own;
        if (own == 0 || (direction && own != direction)) return 0;
        direction = own;
    }
    if (failure) return 0;
    if (direction >= 0 && total.num > 0) return 1;
    if (direction <= 0 && total.num < 0) return -1;
    return 0;
}

/* Divide il monomio m in esponenziali complessi e resto. Mette in *wave i
 * fattori e^{i M} di m e in *angle l'angolo complessivo, cioè la somma degli
 * esponenti: il prodotto dei fattori di *wave vale e^{i angle}. Ritorna 1 se
 * ci riesce; 0 se tra gli esponenziali ce n'è uno a cui si applicano le
 * identità con pi greco (4f, 4g), che qui non si sanno trattare. */
static int split_wave(const Mono *m, Mono *wave, Poly *angle) {
    wave->count = 0;
    *angle = poly_const(num_int(0));
    for (int f = 0; f < m->count; f++) {
        const Atom *a = &atoms[m->factor[f].atom];
        if (a->kind != ATOM_POW || a->base != BASE_EI) continue;
        if (a->pi != PI_NONE) return 0;
        Term t;
        t.coef = num_frac(m->factor[f].exp);
        t.mono = a->exponent;
        *angle = poly_add(*angle, poly_term(t), 0);
        wave->factor[wave->count++] = m->factor[f];
    }
    return 1;
}

/* Ritorna il termine t privato dei fattori di wave. */
static Term term_without(Term t, const Mono *wave) {
    for (int f = 0; f < wave->count; f++) t.mono = mono_with_exponent(&t.mono, wave->factor[f].atom, frac_int(0));
    return t;
}

/* Ritorna 1 se l'atomo vale un numero algebrico per ogni n intero: n, i
 * termini delle successioni per ricorrenza, e le potenze con base algebrica
 * ed esponente razionale, come 2^n o la radice di n + 1. Non lo sono, o non
 * si sa, pi greco, i logaritmi, le arcotangenti, le somme, i parametri.
 * Serve alla regola 13c-8. */
static int poly_is_algebraic(Poly p);
static int atom_is_algebraic(int atom) {
    const Atom *a = &atoms[atom];
    if (a->kind == ATOM_VAR) return a->id == induction_var;
    if (a->kind == ATOM_REC) return 1;
    if (a->kind != ATOM_POW || a->base == BASE_EI || !mono_is_integer(&a->exponent)) return 0;
    if (a->base == BASE_ATOM) return atom_is_algebraic((int)a->id);
    return a->base == BASE_PRIME || poly_is_algebraic(base_polys[a->id]);
}

/* Ritorna 1 se ogni atomo del monomio vale un numero algebrico. */
static int mono_is_algebraic(const Mono *m) {
    for (int i = 0; i < m->count; i++)
        if (!atom_is_algebraic(m->factor[i].atom)) return 0;
    return 1;
}

/* Ritorna 1 se ogni atomo di p vale un numero algebrico. */
static int poly_is_algebraic(Poly p) {
    for (int i = 0; i < p.count; i++)
        if (!mono_is_algebraic(&p.term[i].mono)) return 0;
    return 1;
}

/* 13c-8. Ritorna 1 se q, che contiene esponenziali complessi e^{i M}, è
 * certamente diverso da zero per ogni intero n >= base; -1 se non lo sa
 * stabilire. È il caso dei denominatori con seni e coseni, come sin(n x) con
 * x legato a un numero razionale.
 *
 * Teorema di Lindemann-Weierstrass: se t_1, ..., t_r sono numeri algebrici
 * distinti, allora e^{t_1}, ..., e^{t_r} sono linearmente indipendenti sui
 * numeri algebrici: una loro combinazione a coefficienti algebrici vale zero
 * solo se tutti i coefficienti sono zero. (Ne segue, per esempio, che sin(1)
 * non è zero, cioè che pi greco non è razionale.)
 *
 * Si scrive q = g_1 e^{i t_1} + ... + g_r e^{i t_r}, raccogliendo i termini
 * con gli stessi esponenziali: ogni t_j è la somma degli esponenti, un
 * polinomio negli atomi, e ogni g_j è il polinomio che resta. Se tutti gli
 * atomi coinvolti sono algebrici, per ogni n intero i t_j e i g_j sono numeri
 * algebrici. Basta allora un indice j tale che, per ogni n >= base, g_j non
 * sia zero e t_j sia diverso da tutti gli altri t_k: anche se altri
 * esponenti coincidono tra loro, e^{i t_j} resta con il suo coefficiente non
 * nullo, e la somma non può annullarsi. Le due richieste sono a loro volta
 * condizioni "mai zero", decise da condition_holds(). */
static int exponentials_never_cancel(Poly q, long long base) {
    enum { MOST = 24 };
    Mono wave[MOST];   /* gli esponenziali di ogni termine */
    Poly angle[MOST];  /* il loro esponente complessivo t */
    long long where;
    if (q.count > MOST) return -1;

    /* Ogni termine si divide in esponenziali e resto, tutti algebrici. */
    int waves = 0;
    for (int i = 0; i < q.count; i++) {
        if (!split_wave(&q.term[i].mono, &wave[i], &angle[i])) return -1;
        Term rest = term_without(q.term[i], &wave[i]);
        if (!mono_is_algebraic(&rest.mono) || !poly_is_algebraic(angle[i])) return -1;
        waves += wave[i].count;
    }
    if (!waves || failure) return -1;

    /* Si cerca il termine j che non può essere cancellato. */
    for (int j = 0; j < q.count; j++) {
        int alone = 1, repeated = 0;
        Poly g = poly_const(num_int(0));
        for (int k = 0; k < j; k++)
            if (mono_cmp(&wave[k], &wave[j]) == 0) repeated = 1;
        if (repeated) continue;

        /* Il coefficiente g_j, e gli esponenti degli altri gruppi. */
        for (int k = 0; k < q.count && alone; k++) {
            if (mono_cmp(&wave[k], &wave[j]) == 0) {
                g = poly_add(g, poly_term(term_without(q.term[k], &wave[k])), 0);
            } else {
                alone = condition_holds(NEVER_ZERO, poly_add(angle[j], angle[k], 1), base, &where) == 1;
            }
        }
        if (failure) return -1;
        if (alone && condition_holds(NEVER_ZERO, g, base, &where) == 1) return 1;
    }
    return -1;
}

/* 13c-1. IL SEGNO DI UN SENO O DI UN COSENO
 *
 * Seni e coseni sono calcolati come esponenziali complessi (capitolo 11), e
 * in quella forma il segno non si vede. Lo si ritrova riconoscendo le due
 * forme più semplici:
 *
 *     c e^{i t} + c e^{-i t}      = 2 c cos t
 *     -i c e^{i t} + i c e^{-i t} = 2 c sin t
 *
 * eventualmente moltiplicate per un fattore positivo, come 2^n. Il segno di
 * cos t e di sin t dipende dal quadrante: dall'intero m per cui
 *
 *     m pi/2 < t < (m + 1) pi/2.
 *
 * Con m = 0 sono positivi entrambi, con m = 1 solo il seno, con m = 2
 * nessuno dei due, con m = 3 solo il coseno, e poi si ricomincia.
 *
 * Quando l'angolo dipende da n il quadrante deve essere lo stesso per ogni
 * n: le due disuguaglianze sono a loro volta condizioni "positivo per ogni
 * n", decise da condition_holds(). Se l'angolo è un multiplo di pi greco,
 * t = pi r, si chiede m < 2 r < m + 1, senza approssimazioni. Altrimenti
 * servono dei numeri razionali tra cui stia pi greco, e si usano quelli di
 * Archimede, 223/71 < pi < 22/7: per m positivo basta t > m (22/7)/2 da una
 * parte e t < (m + 1) (223/71)/2 dall'altra, e per m negativo i due limiti
 * si scambiano. Sono condizioni un po' più strette del necessario: un angolo
 * molto vicino a un multiplo di pi/2 resta senza risposta. */

/* Cerca il quadrante dell'angolo `angle` per ogni n >= base: ritorna 1 e
 * mette in *quadrant l'intero m descritto sopra, se lo trova tra -8 e 8;
 * altrimenti ritorna 0. Se in_pi è diverso da zero l'angolo vero è pi greco
 * per `angle`. */
static int angle_quadrant(Poly angle, int in_pi, long long base, int *quadrant) {
    const Frac below = {223, 71}, above = {22, 7};
    long long where;
    for (int step = 0; step <= 16 && !failure; step++) {
        /* I candidati nell'ordine 0, 1, -1, 2, -2, ... */
        int m = step % 2 ? (step + 1) / 2 : -(step / 2);
        Frac low = frac_int(m), high = frac_int(m + 1);
        if (!in_pi) {
            low = frac_mul(low, frac_div(m >= 0 ? above : below, frac_int(2)));
            high = frac_mul(high, frac_div(m + 1 > 0 ? below : above, frac_int(2)));
        }

        /* scaled è 2 r per un multiplo di pi greco, l'angolo stesso altrimenti. */
        Poly scaled = in_pi ? poly_mul(angle, poly_const(num_int(2))) : angle;
        if (condition_holds(ALWAYS_POSITIVE, poly_add(scaled, poly_const(num_frac(low)), 1), base, &where) != 1) continue;
        if (condition_holds(ALWAYS_POSITIVE, poly_add(poly_const(num_frac(high)), scaled, 1), base, &where) != 1) continue;
        *quadrant = m;
        return 1;
    }
    return 0;
}

/* Ritorna il segno di p per ogni n >= base, +1 o -1, quando p è una delle
 * forme descritte sopra; 0 se non lo è o se il quadrante non si trova. Mette
 * in *strict 1 se il segno è stretto, 0 se p può anche valere zero.
 *
 * Oltre alle due forme con seno e coseno ne riconosce una terza, con un
 * termine costante: c0 + c e^{i t} + (coniugato di c) e^{-i t}, che vale
 * c0 + 2 Re(c e^{i t}) e sta quindi tra c0 - 2|c| e c0 + 2|c|. Se |c0| supera
 * 2|c| ha il segno di c0; se lo uguaglia lo ha in senso largo. È il caso di
 * cos^2 t = 1/2 + (e^{2 i t} + e^{-2 i t})/4, che nasce come denominatore di
 * una tangente al quadrato. */
static int trig_sign(Poly p, long long base, int *strict) {
    Mono wave[3];
    Poly angle[3];
    Term rest[3];
    int still = -1, first = -1, second = -1, quadrant;
    if (p.count < 2 || p.count > 3) return 0;

    /* Due termini con esponenziali opposti, e al più uno senza. */
    for (int i = 0; i < p.count; i++) {
        if (!split_wave(&p.term[i].mono, &wave[i], &angle[i])) return 0;
        rest[i] = term_without(p.term[i], &wave[i]);
        if (wave[i].count == 0 && still < 0) still = i;
        else if (first < 0) first = i;
        else second = i;
    }
    if (second < 0 || wave[first].count == 0 || wave[second].count == 0 || (p.count == 3 && still < 0)) return 0;
    if (mono_mul(&wave[first], &wave[second]).count != 0) return 0;

    /* Lo stesso fattore reale in tutti i termini, positivo; i coefficienti
     * dei due esponenziali coniugati tra loro. */
    Num c = rest[first].coef, d = rest[second].coef;
    if (mono_cmp(&rest[first].mono, &rest[second].mono) != 0 || frac_cmp(c.re, d.re) != 0 || frac_cmp(c.im, frac_neg(d.im)) != 0) return 0;
    for (int f = 0; f < rest[first].mono.count; f++)
        if (!atom_is_positive(rest[first].mono.factor[f].atom, base)) return 0;

    /* Con il termine costante: il confronto tra c0^2 e 4 |c|^2. */
    if (p.count == 3) {
        Num c0 = rest[still].coef;
        if (mono_cmp(&rest[still].mono, &rest[first].mono) != 0 || c0.im.num != 0) return 0;
        Frac size = frac_mul(frac_int(4), frac_add(frac_mul(c.re, c.re), frac_mul(c.im, c.im)));
        int compare = frac_cmp(frac_mul(c0.re, c0.re), size);
        if (failure || compare < 0) return 0;
        *strict = compare > 0;
        return c0.re.num > 0 ? 1 : -1;
    }

    /* L'angolo è un multiplo di pi greco se pi compare, alla prima potenza,
     * in tutti i suoi termini; se compare solo in alcuni si rinuncia. */
    int pi = atom_var(VAR_PI), with = 0;
    Poly turn = angle[first];
    for (int i = 0; i < turn.count; i++) with += frac_cmp(mono_exponent(&turn.term[i].mono, pi), frac_int(1)) == 0;
    if (with != 0 && with != turn.count) return 0;
    if (with) {
        Term divisor;
        divisor.coef = num_int(1);
        divisor.mono = mono_atom(pi, frac_int(-1));
        turn = poly_mul(turn, poly_term(divisor));
    }
    if (failure || !angle_quadrant(turn, with != 0, base, &quadrant)) return 0;

    /* Coefficiente reale: coseno. Immaginario: seno, con il segno di -Im c,
     * perché -i c' e^{i t} + i c' e^{-i t} = 2 c' sin t. */
    int q = ((quadrant % 4) + 4) % 4;
    *strict = 1;
    if (c.im.num == 0) return (c.re.num > 0 ? 1 : -1) * (q == 0 || q == 3 ? 1 : -1);
    if (c.re.num == 0) return (c.im.num < 0 ? 1 : -1) * (q == 0 || q == 1 ? 1 : -1);
    return 0;
}

/* 13c-7. IL SEGNO PER DIFFERENZE
 *
 * Per le espressioni fatte di n e di potenze come 2^n e 3^n, dove più
 * quantità crescono a velocità diverse: 2^n - n, 3^n - 2^n - n.
 *
 * Lemma. Sia b > 0. Se q(N) > 0 e q(n+1) - b q(n) >= 0 per ogni n >= N,
 * allora q(n) > 0 per ogni n >= N: per induzione, q(n+1) >= b q(n) > 0. Lo
 * stesso vale con >= al posto di >.
 *
 * La differenza q(n+1) - b q(n) è un'espressione dello stesso tipo, e più
 * semplice: se b è la più piccola delle basi che compaiono in q (1 per i
 * termini che sono polinomi in n), i termini con quella base perdono un
 * grado, perché b^{n+1} (n+1)^d - b b^n n^d = b^{n+1} ((n+1)^d - n^d), e
 * dopo abbastanza passi spariscono. Si ripete finché resta un'espressione di
 * segno evidente. Per 2^n - n: la differenza con b = 1 è 2^n - 1, la
 * successiva 2^n, che è positiva; e i valori in n = 1 sono 1 e 1, positivi.
 *
 * Il lemma chiede che ogni differenza parta bene in N. Se non succede per
 * N = base si prova più avanti, controllando uno per uno i valori saltati:
 * così 2^n - 100 n - 1000, negativo all'inizio e poi sempre positivo, risulta
 * mai nullo, e di 2^n - n^2 si trova che vale zero per n = 2. */

/* Ritorna 1 se q è fatto solo di n e di potenze p^n di numeri primi, con
 * esponenti interi non negativi e coefficienti reali. */
static int in_growth_class(Poly q) {
    for (int i = 0; i < q.count; i++) {
        if (q.term[i].coef.im.num != 0) return 0;
        for (int f = 0; f < q.term[i].mono.count; f++) {
            const Factor *factor = &q.term[i].mono.factor[f];
            const Atom *a = &atoms[factor->atom];
            int power = a->kind == ATOM_POW && a->base == BASE_PRIME && a->exponent.count == 1 &&
                        a->exponent.factor[0].atom == atom_var(induction_var) && frac_cmp(a->exponent.factor[0].exp, frac_int(1)) == 0;
            int letter = a->kind == ATOM_VAR && a->id == induction_var;
            if ((!power && !letter) || factor->exp.den != 1 || factor->exp.num < 0 || factor->exp.num > MAX_UNIVARIATE) return 0;
        }
    }
    return 1;
}

/* Ritorna q(n+1) scritto con gli stessi atomi, per q della classe di
 * in_growth_class(): n diventa n + 1 e ogni p^n diventa p p^n. */
static Poly poly_shift(Poly q) {
    int n = atom_var(induction_var);
    Poly out = poly_substitute(q, n, rat_add(rat_atom(n), rat_int(1), 0)).num;
    for (int x = 0; x < atom_count && !failure; x++) {
        if (atoms[x].kind != ATOM_POW || atoms[x].base != BASE_PRIME || atoms[x].exponent.count == 0) continue;
        out = poly_substitute(out, x, rat_mul(rat_int(atoms[x].id), rat_atom(x))).num;
    }
    return out;
}

/* Mette in *value il valore di q per n = at, e ritorna 1; ritorna 0 se non è
 * un razionale che si sa calcolare (vedi mono_at()). */
static int poly_at(Poly q, long long at, Frac *value) {
    Frac v;
    *value = frac_int(0);
    for (int i = 0; i < q.count; i++) {
        if (q.term[i].coef.im.num != 0 || !mono_at(&q.term[i].mono, at, &v)) return 0;
        *value = frac_add(*value, frac_mul(q.term[i].coef.re, v));
    }
    return !failure;
}

/* Ritorna 1 se il lemma qui sopra dimostra che q(n) > 0 (strict) o q(n) >= 0
 * per ogni n >= from; 0 se non ci riesce. depth limita il numero di
 * differenze successive. */
static int grows_positive(Poly q, long long from, int strict, int depth) {
    Frac value;
    if (q.count == 0) return !strict;
    if (!poly_at(q, from, &value) || value.num < 0 || (strict && value.num == 0)) return 0;
    int evident = evident_sign(q, from);
    if (evident || depth == 0) return evident > 0;

    /* La base più piccola tra i termini: il prodotto dei primi di ciascuno. */
    long long smallest = 0;
    for (int i = 0; i < q.count; i++) {
        long long own = 1;
        for (int f = 0; f < q.term[i].mono.count; f++) {
            const Atom *a = &atoms[q.term[i].mono.factor[f].atom];
            for (long long e = a->kind == ATOM_POW ? q.term[i].mono.factor[f].exp.num : 0; e > 0; e--)
                if (__builtin_mul_overflow(own, a->id, &own)) return 0;
        }
        if (!smallest || own < smallest) smallest = own;
    }
    Poly next = poly_add(poly_shift(q), poly_mul(q, poly_const(num_int(smallest))), 1);
    return !failure && grows_positive(next, from, 0, depth - 1);
}

/* Decide con il lemma se q, della classe di in_growth_class(), rispetta kind
 * per ogni n >= base: 1, 0 (con il primo n in cui fallisce in *where) o -1. */
static int difference_rule(Requirement kind, Poly q, long long base, long long *where) {
    Poly minus = poly_add(poly_const(num_int(0)), q, 1);
    if (!in_growth_class(q)) return -1;
    for (long long from = base; from <= base + 64; from++) {
        /* Il valore in `from`, calcolato: i precedenti sono già stati visti. */
        Frac value;
        if (!poly_at(q, from, &value)) return -1;
        if (kind == NEVER_ZERO ? value.num == 0 : kind == ALWAYS_POSITIVE ? value.num <= 0 : value.num < 0) {
            *where = from;
            return 0;
        }

        /* Da qui in poi il segno non cambia più? */
        if (grows_positive(q, from, kind != NEVER_NEGATIVE, 40)) return 1;
        if (kind == NEVER_ZERO && grows_positive(minus, from, 1, 40)) return 1;
        if (failure) return -1;
    }
    return -1;
}

/* Decide se il polinomio negli atomi p rispetta kind per ogni intero
 * n >= base: ritorna 1 se sì, 0 se no (e mette in *where un n in cui
 * fallisce), -1 se non lo sa stabilire. Le regole sono descritte in testa al
 * paragrafo 13c. */
int condition_holds(Requirement kind, Poly p, long long base, long long *where) {
    long long c[MAX_UNIVARIATE + 1], scale;
    *where = base;

    /* Lo zero, anche quando lo è per un'identità che solo il test di
     * annullamento riconosce: dividere per arctan(1/2) + arctan(1/3) - pi/4
     * è dividere per zero. */
    if (poly_vanishes(p)) return kind == NEVER_NEGATIVE;
    if (failure) return -1;

    /* 13c-1. Un seno o un coseno: il segno viene dal quadrante. Un segno in
     * senso largo basta per "non negativo"; per "positivo" bisogna anche che
     * p non si annulli, e lo dicono le altre regole. */
    int strict = 0, trig = trig_sign(p, base, &strict);
    if (failure) return -1;
    *where = base;
    if (trig && strict) return kind == NEVER_ZERO || trig > 0;
    if (trig > 0 && kind == NEVER_NEGATIVE) return 1;
    if (trig > 0 && kind == ALWAYS_POSITIVE) return condition_holds(NEVER_ZERO, p, base, where) == 1 ? 1 : -1;
    if (trig < 0 && kind == ALWAYS_POSITIVE) return 0;

    /* 13c-2. Il monomio comune. */
    Mono common = poly_common(p);
    for (int i = 0; i < common.count; i++) {
        int atom = common.factor[i].atom;
        int fine = kind == NEVER_ZERO ? atom_never_zero(atom, base, where) : (atom_is_positive(atom, base) ? 1 : -1);
        if (fine != 1) return fine;
    }
    Term divisor;
    divisor.coef = num_int(1);
    divisor.mono = mono_pow(&common, frac_int(-1));
    Poly q = poly_mul(p, poly_term(divisor));
    if (failure) return -1;
    *where = base;

    /* 13c-3. Un polinomio nella sola variabile principale: il segno si
     * decide. */
    int atom = main_atom(q, base);
    int degree = atom >= 0 ? poly_coefficients(q, atom, c, &scale) : -1;
    if (degree >= 0 && kind != NEVER_ZERO) {
        int holds = sign_holds(c, degree, kind == ALWAYS_POSITIVE, atom, base, where);
        if (holds >= 0) return holds;
    }

    /* 13c-4. La variabile principale e radici di primi: gli zeri si trovano. */
    if (atom >= 0 && kind == NEVER_ZERO) {
        int free = zero_free(q, atom, base, where);
        if (free >= 0) return free;
    }
    if (failure) return -1;
    *where = base;

    /* 13c-5, 13c-6. Un segno evidente, o garantito dall'andamento. Una
     * espressione sempre negativa non si annulla, ma non è né positiva né
     * non negativa, già per n = base. */
    int sign = evident_sign(q, base);
    if (!sign) sign = monotone_sign(q, base);
    if (failure) return -1;
    if (sign > 0) return 1;
    if (sign < 0) return kind == NEVER_ZERO;

    /* 13c-7. n e potenze come 2^n: il segno per differenze. */
    int grown = difference_rule(kind, q, base, where);
    if (grown >= 0) return grown;
    if (failure) return -1;
    *where = base;

    /* 13c-8. Esponenziali complessi che non si cancellano. */
    return kind == NEVER_ZERO ? exponentials_never_cancel(q, base) : -1;
}

/* Decide una condizione dell'elenco per ogni n >= base: 1, 0 (con un n in cui
 * fallisce in *where) o -1. Prima sul prodotto dei suoi fattori; se così non
 * si decide, e i fattori sono più d'uno, sul segno di ciascuno: il prodotto
 * di fattori che hanno ognuno un segno fisso ha un segno fisso. */
int condition_decided(const Condition *c, long long base, long long *where) {
    Poly product = c->factor[0];
    for (int f = 1; f < c->count; f++) product = poly_mul(product, c->factor[f]);
    int holds = failure ? -1 : condition_holds(c->kind, product, base, where);
    if (holds >= 0 || c->count == 1 || c->kind == NEVER_ZERO || failure) return holds;

    int sign = 1;
    for (int f = 0; f < c->count; f++) {
        Poly minus = poly_add(poly_const(num_int(0)), c->factor[f], 1);
        if (condition_holds(ALWAYS_POSITIVE, c->factor[f], base, where) == 1) continue;
        if (failure || condition_holds(ALWAYS_POSITIVE, minus, base, where) != 1) return -1;
        sign = -sign;
    }
    *where = base;
    return sign > 0;
}

/* Decide se l'enunciato, con i parametri legati ai valori del punto in uso, è
 * definito per ogni n >= base: ritorna 1 se sì, 0 se no (con un n in cui non
 * lo è in *where e il perché in *why), -1 se non lo sa stabilire. Vedi il
 * paragrafo 13c.
 *
 * Le valutazioni sono tre, e dicono a quale n si riferisce una condizione
 * che fallisce: quelle nate dal calcolo di D(n) a quell'n, quelle nate solo
 * da D(n+1) al successivo, quelle nate solo da D(base) al caso base. La
 * terza serve perché il calcolo con i numeri non controlla tutto: un
 * logaritmo di cos(1) non è un numero, e il suo segno lo decide solo
 * condition_holds(). */
int defined_for_every(const Statement *statement, long long base, long long *where, const char **why) {
    Rat n = rat_atom(atom_var(induction_var));
    int answer = 1, broken = 0;

    /* Le tre valutazioni, con l'elenco delle condizioni acceso. */
    condition_count = conditions_lost = 0;
    conditions_on = 1;
    difference(statement, n);
    int first = condition_count;
    difference(statement, rat_add(n, rat_int(1), 0));
    int second = condition_count;
    difference(statement, rat_int(base));
    conditions_on = 0;
    if (failure || conditions_lost) answer = -1;
    failure = NULL;

    /* Ogni condizione va decisa. Una che fallisce chiude la questione, ma si
     * guardano tutte, per riferire il più piccolo n in cui qualcosa manca. */
    for (int i = 0; i < condition_count; i++) {
        long long at;
        int holds = condition_decided(&conditions[i], base, &at);
        if (failure) holds = -1;
        failure = NULL;
        if (holds < 0) answer = -1;
        if (holds != 0) continue;
        at = i >= second ? base : at + (i >= first);
        if (!broken || at < *where) { *where = at; *why = conditions[i].why; }
        broken = 1;
    }
    return broken ? 0 : answer;
}

/* Ritorna la posizione nel vocabolario della successione di cui l'atomo BIGOP
 * `atom` è la definizione, o -1 se è una somma scritta nell'enunciato. */
static int bigop_library(int atom) {
    for (int i = 0; i < LIBRARY_COUNT; i++)
        if (library[i].tree == atoms[atom].node) return i;
    return -1;
}

/* 13d. DEFINITO PER PARAMETRI ABBASTANZA GRANDI
 *
 * Il paragrafo 13c cerca un valore dei parametri che vada bene per ogni n.
 * Non sempre esiste: la somma dei ln(x - k) per k da 1 a n è definita per
 * x > n, e nessun x supera tutti gli n. Eppure per ogni n i valori buoni ci
 * sono: tutti quelli abbastanza grandi. È ciò che serve perché l'enunciato
 * non sia vuoto per nessun n, e qui lo si dimostra così.
 *
 * Un polinomio in x, per x abbastanza grande, ha il segno del suo
 * coefficiente di grado massimo (oltre il limite di Cauchy non ha più
 * radici). Una condizione di esistenza che è un polinomio in x con
 * coefficienti in n vale quindi "da un certo x in poi" se il coefficiente di
 * grado massimo ha il segno giusto: e questo, non contenendo più x, è una
 * condizione in n che condition_holds() sa decidere per ogni n.
 *
 * Le condizioni sono in numero finito per ogni n: i due membri in n e in
 * n + 1, e i termini delle somme, uno per ogni indice fino a n + 1. Ognuna
 * vale oltre una sua soglia, quindi tutte insieme oltre la più grande. Per i
 * termini delle somme la condizione si scrive una volta sola, con l'indice
 * generico "estremo inferiore + t" e t >= 0, come fa body_is_positive().
 *
 * Con più parametri si mandano all'infinito uno dopo l'altro: il primo
 * dell'elenco molto più in fretta del secondo, e così via. Conta allora il
 * coefficiente di grado massimo nel primo parametro, poi in quello il
 * coefficiente di grado massimo nel secondo. Si provano i due ordini
 * estremi, e i due versi: tutti verso più infinito, tutti verso meno
 * infinito (dove una potenza dispari cambia segno). */

/* I parametri mandati all'infinito, dal più veloce al più lento, e il verso:
 * +1 verso più infinito, -1 verso meno infinito. Vuoto fuori da
 * defined_eventually(). */
static int far_name[MAX_POINT];
static int far_count;
static int far_sign;

/* Ritorna 1 se la lettera name è uno dei parametri mandati all'infinito. */
static int is_far(long long name) {
    for (int i = 0; i < far_count; i++)
        if (far_name[i] == name) return 1;
    return 0;
}

/* Ritorna 1 se nel sotto-albero node compare, libero, uno di quei parametri.
 * shadow elenca gli indici di somma che nascondono una lettera con lo stesso
 * nome, come in uses_bound_variable(). */
static int node_has_parameter(const Node *node, const NameScope *shadow) {
    if (!node) return 0;
    if (node->kind == N_VAR) return !name_shadowed(shadow, node->name) && is_far(node->name);
    if (node->kind == N_BIGOP) {
        if (node_has_parameter(node->a, shadow) || node_has_parameter(node->b, shadow)) return 1;
        NameScope inner = {node->name, shadow};
        return node_has_parameter(node->c, &inner);
    }
    return node_has_parameter(node->a, shadow) || node_has_parameter(node->b, shadow) ||
           node_has_parameter(node->c, shadow);
}

static int poly_has_parameter(Poly p);

/* Ritorna 1 se il valore dell'atomo dipende da uno dei parametri mandati
 * all'infinito, anche di nascosto: nel termine di una somma, nella base di
 * una potenza o di un logaritmo, nell'argomento di un'arcotangente. */
static int atom_has_parameter(int atom) {
    const Atom *a = &atoms[atom];
    if (a->kind == ATOM_VAR) return is_far(a->id);
    if (a->kind == ATOM_REC) return 0;
    if (a->kind == ATOM_BIGOP) return bigop_library(atom) < 0 && node_has_parameter(a->node, NULL);
    if (a->kind == ATOM_ATAN) return poly_has_parameter(atan_args[a->id].num) || poly_has_parameter(atan_args[a->id].den);
    for (int f = 0; f < a->exponent.count; f++)
        if (atom_has_parameter(a->exponent.factor[f].atom)) return 1;
    if (a->base == BASE_ATOM) return atom_has_parameter((int)a->id);
    return a->base == BASE_POLY && poly_has_parameter(base_polys[a->id]);
}

/* Ritorna 1 se p contiene un atomo che dipende da uno di quei parametri. */
static int poly_has_parameter(Poly p) {
    for (int i = 0; i < p.count; i++)
        for (int f = 0; f < p.term[i].mono.count; f++)
            if (atom_has_parameter(p.term[i].mono.factor[f].atom)) return 1;
    return 0;
}

static int eventual_sign(Poly p, long long base);

/* Ritorna 1 se il prodotto dell'atomo BIGOP `atom` ha tutti i fattori
 * positivi per parametri abbastanza grandi: il corpo, valutato nell'indice
 * generico, ha numeratore e denominatore dello stesso segno. Allora per ogni
 * n il prodotto, che ha un numero finito di fattori, è positivo da un certo
 * punto in poi. Un errore durante la prova non riguarda l'enunciato. */
static int product_far_positive(int atom, long long base) {
    const Node *node = atoms[atom].node;
    const char *saved = failure;
    long long lower;
    int positive = 0;
    env_count = 0;
    library_depth = 0;
    if (node->op && rat_integer(eval(node->a), &lower)) {
        Rat value = eval_body(node, rat_add(rat_int(lower), rat_atom(atom_var(VAR_SLACK)), 0));
        int above = failure ? 0 : eventual_sign(value.num, base), below = failure ? 0 : eventual_sign(value.den, base);
        positive = above * below == 1;
    }
    failure = saved;
    return positive;
}

/* Ritorna il segno che p finisce per avere, per ogni n >= base, quando i
 * parametri sono abbastanza grandi nel verso e nell'ordine in uso: +1 o -1;
 * 2 se si sa solo che non si annulla; 0 se non si sa dire nulla.
 *
 * p si scrive come monomio comune per il resto. Nel monomio comune ogni
 * atomo deve avere un segno noto: i parametri stessi, gli atomi senza
 * parametri di cui 13c conosce il segno, i prodotti di fattori positivi, le
 * potenze di una base positiva. Il resto deve essere un polinomio nei
 * parametri: conta il suo coefficiente di grado massimo, che non li contiene
 * più. */
static int eventual_sign(Poly p, long long base) {
    long long where;
    if (p.count == 0) return 0;

    /* Senza parametri: una condizione in n, da decidere per ogni n. */
    if (!poly_has_parameter(p)) {
        if (condition_holds(ALWAYS_POSITIVE, p, base, &where) == 1) return 1;
        if (condition_holds(ALWAYS_POSITIVE, poly_add(poly_const(num_int(0)), p, 1), base, &where) == 1) return -1;
        return condition_holds(NEVER_ZERO, p, base, &where) == 1 ? 2 : 0;
    }

    /* Il monomio comune. */
    int sign = 1, known = 1;
    Mono common = poly_common(p);
    for (int i = 0; i < common.count; i++) {
        int atom = common.factor[i].atom;
        const Atom *a = &atoms[atom];
        Frac e = common.factor[i].exp;
        if (a->kind == ATOM_VAR && is_far(a->id)) {
            if (far_sign < 0 && e.den != 1) return 0;
            if (far_sign < 0 && e.num % 2) sign = -sign;
        } else if (!atom_has_parameter(atom)) {
            if (atom_is_positive(atom, base)) continue;
            if (atom_never_zero(atom, base, &where) != 1) return 0;
            known = 0;
        } else if (a->kind == ATOM_POW && a->base == BASE_EI) {
            known = 0;
        } else if (a->kind == ATOM_BIGOP) {
            if (!product_far_positive(atom, base)) return 0;
        } else if (a->kind != ATOM_POW || a->base != BASE_POLY || eventual_sign(base_polys[a->id], base) != 1) {
            return 0;
        }
    }
    Term divisor;
    divisor.coef = num_int(1);
    divisor.mono = mono_pow(&common, frac_int(-1));
    Poly lead = poly_mul(p, poly_term(divisor));

    /* Il coefficiente di grado massimo, un parametro dopo l'altro. */
    for (int i = 0; i < far_count && !failure; i++) {
        Poly part[MAX_UNIVARIATE + 1];
        int degree = poly_split(lead, atom_var(far_name[i]), part, MAX_UNIVARIATE);
        if (degree < 0) return 0;
        if (far_sign < 0 && degree % 2) sign = -sign;
        lead = part[degree];
    }
    if (failure || poly_has_parameter(lead)) return 0;
    int tail = eventual_sign(lead, base);
    if (tail == 0) return 0;
    return tail == 2 || !known ? 2 : sign * tail;
}

/* Ritorna 1 se per ogni n >= base l'enunciato è definito per tutti i valori
 * dei parametri abbastanza grandi, in uno dei versi e degli ordini provati;
 * -1 se non riesce a stabilirlo. I parametri sono quelli di point_name[].
 * Vedi il paragrafo 13d. */
static int defined_eventually(const Statement *statement, long long base) {
    Rat n = rat_atom(atom_var(induction_var));
    int count = point_count, known = atom_count, found = 0;

    /* Le condizioni, con i parametri come lettere: i due membri in n e in
     * n + 1, e il termine generico di ogni somma e prodotto. */
    point_count = 0;
    condition_count = conditions_lost = 0;
    conditions_on = 1;
    failure = NULL;
    difference(statement, n);
    difference(statement, rat_add(n, rat_int(1), 0));
    for (int x = 0; x < known && !failure; x++) {
        long long lower;
        if (atoms[x].kind != ATOM_BIGOP) continue;
        env_count = 0;
        library_depth = 0;
        if (!rat_integer(eval(atoms[x].node->a), &lower)) { conditions_lost = 1; break; }
        eval_body(atoms[x].node, rat_add(rat_int(lower), rat_atom(atom_var(VAR_SLACK)), 0));
    }
    conditions_on = 0;
    point_count = count;
    int lost = failure || conditions_lost;
    failure = NULL;

    /* I due ordini e i due versi. Ogni condizione chiede il segno del
     * prodotto dei suoi fattori. */
    far_count = count;
    for (int attempt = 0; attempt < (count > 1 ? 4 : 2) && !found && !lost; attempt++) {
        far_sign = attempt % 2 ? -1 : 1;
        for (int i = 0; i < count; i++) far_name[i] = point_name[attempt < 2 ? i : count - 1 - i];
        found = 1;
        for (int i = 0; i < condition_count && found; i++) {
            const Condition *c = &conditions[i];
            int sign = 1;
            for (int f = 0; f < c->count && found; f++) {
                int own = eventual_sign(c->factor[f], base);
                if (failure || own == 0 || (own == 2 && c->kind != NEVER_ZERO)) found = 0;
                if (own == -1) sign = -sign;
                failure = NULL;
            }
            if (c->kind != NEVER_ZERO && sign < 0) found = 0;
        }
    }
    far_count = 0;
    return found ? 1 : -1;
}

/* I numeri semplici che la verifica numerica dà ai parametri: positivi e
 * negativi, interi e frazioni, grandi e piccoli. */
static const Frac point_samples[] = {{2, 1}, {3, 1}, {1, 2}, {5, 1}, {1, 3}, {-2, 1}, {3, 2}, {7, 1},
                                     {-1, 2}, {4, 1}, {-3, 1}, {1000, 1}, {1, 1000}};
enum { POINT_SAMPLES = sizeof point_samples / sizeof *point_samples };

/* Ritorna lo stato di adesso, da ridare a scratch_drop() dopo il conto. */
Scratch scratch_mark(void) { return (Scratch){atom_count, base_poly_count, atan_count, arena_used}; }

/* Toglie tutto ciò che è nato dopo mark. */
void scratch_drop(Scratch mark) {
    atom_count = mark.atoms;
    base_poly_count = mark.polys;
    atan_count = mark.atans;
    arena_used = mark.arena;
}

/* I VALORI DEI PARAMETRI SCELTI GUARDANDO LE CONDIZIONI
 *
 * La verifica numerica (13e) prova per i parametri pochi numeri semplici. Un
 * enunciato definito solo per valori particolari, come la radice di
 * x - 5000, non ne incontrerebbe mai uno buono. Quando i numeri semplici non
 * bastano si guarda che cosa l'enunciato chiede: le condizioni di esistenza
 * raccolte con i parametri lasciati come lettere sono, nei casi comuni,
 * polinomi nei parametri. Per ogni parametro, uno alla volta, le condizioni
 * che contengono solo lui dividono la retta in intervalli, separati dalle
 * radici reali dei polinomi: il segno di ogni polinomio è costante dentro un
 * intervallo, quindi basta provare un punto per intervallo.
 *
 * Le radici si cercano in virgola mobile, il solo punto del programma in cui
 * non si usa l'aritmetica esatta. Non è un rischio: servono solo a proporre
 * dei candidati. Ogni candidato viene poi controllato con conti esatti, qui
 * e nella verifica vera e propria. Un errore di arrotondamento può far
 * perdere un candidato buono, mai farne accettare uno cattivo. */

/* Mette in root[], in ordine crescente, le radici reali del polinomio
 * c[0] + c[1] x + ... + c[degree] x^degree, approssimate, e ne ritorna il
 * numero. root deve avere almeno max(degree, 1) posti.
 *
 * Tra due zeri consecutivi della derivata il polinomio è monotono, quindi ha
 * al più una radice, e c'è esattamente quando il segno agli estremi è
 * diverso: la si trova per bisezione. Gli zeri della derivata, che ha un
 * grado in meno, si trovano allo stesso modo, fino al grado 1. Agli estremi
 * della retta fa da confine il limite di Cauchy (vedi sign_holds()). */
static int real_roots(const double *c, int degree, double *root) {
    double derivative[MAX_UNIVARIATE + 1], turn[MAX_UNIVARIATE + 1], bound = 0;
    while (degree > 0 && c[degree] == 0) degree--;
    if (degree < 1) return 0;
    if (degree == 1) { root[0] = -c[0] / c[1]; return 1; }
    for (int i = 0; i < degree; i++) {
        double ratio = c[i] / c[degree];
        if (ratio < 0) ratio = -ratio;
        if (ratio > bound) bound = ratio;
        derivative[i] = (i + 1) * c[i + 1];
    }
    bound += 1;
    int turns = real_roots(derivative, degree - 1, turn), count = 0;

    /* Gli intervalli di monotonia: da -bound al primo zero della derivata, e
     * così via fino a bound. */
    double left = -bound;
    for (int k = 0; k <= turns; k++) {
        double right = k < turns ? turn[k] : bound, at[2] = {left, right}, value[2];
        for (int s = 0; s < 2; s++) {
            value[s] = 0;
            for (int i = degree; i >= 0; i--) value[s] = value[s] * at[s] + c[i];
        }
        if (value[1] == 0) {
            root[count++] = right;
        } else if (value[0] != 0 && (value[0] < 0) != (value[1] < 0)) {
            /* Bisezione: il segno in `low` resta quello di value[0]. */
            double low = left, high = right;
            for (int step = 0; step < 200; step++) {
                double middle = (low + high) / 2, v = 0;
                for (int i = degree; i >= 0; i--) v = v * middle + c[i];
                if ((v < 0) == (value[0] < 0)) low = middle; else high = middle;
            }
            root[count++] = (low + high) / 2;
        }
        left = right;
    }
    return count;
}

/* Ritorna il segno, -1, 0 o 1, del polinomio p nel punto in cui l'atomo
 * `atom` vale y^root, con y razionale: un termine c atom^{a/b} vi vale
 * c y^{a root / b}. Chi chiama garantisce che in p compare solo quell'atomo,
 * con esponenti non negativi il cui denominatore divide root. Il conto è
 * esatto, su interi a 128 bit; se non bastano mette 0 in *known, che chi
 * chiama ha messo a 1.
 *
 * Con y = u/v e K il più grande degli esponenti interi, moltiplicando per
 * v^K e per il minimo comune multiplo L dei denominatori dei coefficienti
 * ogni termine diventa un intero, e il segno non cambia perché v e L sono
 * positivi. */
static int power_sum_sign(Poly p, int atom, long long root, Frac y, int *known) {
    long long top = 0;
    __int128 scale = 1, total = 0;
    for (int i = 0; i < p.count; i++) {
        Frac e = mono_exponent(&p.term[i].mono, atom);
        long long den = p.term[i].coef.re.den;
        if (e.num * (root / e.den) > top) top = e.num * (root / e.den);
        scale = scale / gcd128(scale, den) * den;
        if (scale > COEF_LIMIT) { *known = 0; return 0; }
    }
    for (int i = 0; i < p.count; i++) {
        Frac e = mono_exponent(&p.term[i].mono, atom);
        long long power = e.num * (root / e.den);
        __int128 term = (__int128)p.term[i].coef.re.num * (scale / p.term[i].coef.re.den);
        for (long long k = 0; k < top; k++)
            if (__builtin_mul_overflow(term, (__int128)(k < power ? y.num : y.den), &term)) { *known = 0; return 0; }
        if (__builtin_add_overflow(total, term, &total)) { *known = 0; return 0; }
    }
    return (total > 0) - (total < 0);
}

/* Sceglie per i parametri dell'enunciato dei valori che rispettano le sue
 * condizioni di esistenza, e li mette in point_value[]. Ritorna 1 se ci
 * riesce, 0 se non trova nulla da proporre. Chi chiama deve poi verificare
 * il punto: qui si guardano solo le condizioni che si sanno leggere,
 * calcolate nel primo e nell'ultimo n della verifica numerica.
 *
 * I parametri si fissano uno alla volta. Fissato un valore, lo si sostituisce
 * nelle condizioni, così quelle che legano due parametri diventano
 * condizioni sul secondo.
 *
 * Per il parametro x si sanno leggere le condizioni che sono polinomi in una
 * sola quantità T, anche con esponenti frazionari. Di solito T è x stesso.
 * Ma se l'enunciato contiene la radice di un'espressione di primo grado,
 * come x - 5000, T è quell'espressione: la condizione
 * "radice(x - 5000) > 100" si legge "T^{1/2} > 100". Con gli esponenti
 * frazionari si pone T = y^d, dove d è il minimo comune multiplo dei loro
 * denominatori: le condizioni diventano polinomi in y, e scegliendo y
 * razionale le radici di T sono numeri esatti, che la verifica sa calcolare.
 * Da y si risale a T e poi a x. */
static int choose_point(const Statement *statement, long long base) {
    int count = point_count, useful = 0;

    /* Le condizioni, con i parametri come lettere. Un errore ferma solo la
     * raccolta: si usa ciò che è stato annotato fino a lì. Di una condizione
     * su più fattori conta il prodotto. */
    point_count = 0;
    condition_count = conditions_lost = 0;
    conditions_on = 1;
    failure = NULL;
    difference(statement, rat_int(base));
    failure = NULL;
    difference(statement, rat_int(base + SEARCH_SPAN));
    conditions_on = 0;
    undefined = 0;
    point_count = count;
    for (int i = 0; i < condition_count; i++) {
        for (int f = 1; f < conditions[i].count; f++) conditions[i].factor[0] = poly_mul(conditions[i].factor[0], conditions[i].factor[f]);
        conditions[i].count = 1;
    }
    if (failure) condition_count = 0;
    failure = NULL;

    for (int j = 0; j < count; j++) {
        int x = atom_var(point_name[j]), carrier = x, roots = 0, candidates = 0, chosen = -1;
        long long c[MAX_UNIVARIATE + 1], scale, root = 1;
        Frac slope = frac_int(1), shift = frac_int(0);
        Poly view[MAX_CONDITIONS];
        int usable[MAX_CONDITIONS];
        double real[MAX_CONDITIONS * MAX_UNIVARIATE];
        Frac candidate[POINT_SAMPLES + MAX_CONDITIONS * MAX_UNIVARIATE + 1];

        /* La quantità T: la base di una radice, se è di primo grado in x. */
        for (int i = 0; i < condition_count && carrier == x; i++)
            for (int t = 0; t < conditions[i].factor[0].count && carrier == x; t++)
                for (int f = 0; f < conditions[i].factor[0].term[t].mono.count; f++) {
                    int atom = conditions[i].factor[0].term[t].mono.factor[f].atom;
                    const Atom *a = &atoms[atom];
                    if (a->kind != ATOM_POW || a->base != BASE_POLY || a->exponent.count != 0) continue;
                    if (poly_coefficients(base_polys[a->id], x, c, &scale) != 1) continue;
                    carrier = atom;
                    slope = frac_make(c[1], scale);
                    shift = frac_make(c[0], scale);
                    break;
                }

        /* Le condizioni scritte in T, e quelle che vi si sanno leggere: solo
         * T, con esponenti non negativi. d è il loro denominatore comune. */
        for (int i = 0; i < condition_count; i++) {
            Rat back = rat_div(rat_add(rat_atom(carrier), rat_frac(shift), 1), rat_frac(slope));
            view[i] = carrier == x ? conditions[i].factor[0] : poly_substitute(conditions[i].factor[0], x, back).num;
            usable[i] = !failure;
            failure = NULL;
            for (int t = 0; t < view[i].count && usable[i]; t++) {
                const Term *term = &view[i].term[t];
                Frac e = mono_exponent(&term->mono, carrier);
                usable[i] = term->coef.im.num == 0 && term->mono.count == (e.num != 0) && e.num >= 0 && e.den <= 12;
            }
            for (int t = 0; t < view[i].count && usable[i]; t++) {
                long long den = mono_exponent(&view[i].term[t].mono, carrier).den;
                root = root / (long long)gcd128(root, den) * den;
            }
        }

        /* Le radici reali, in y, dei polinomi a cui si riducono. */
        for (int i = 0; i < condition_count; i++) {
            double coefficient[MAX_UNIVARIATE + 1] = {0};
            int degree = 0;
            for (int t = 0; t < view[i].count && usable[i]; t++) {
                Frac e = mono_exponent(&view[i].term[t].mono, carrier), value = view[i].term[t].coef.re;
                long long power = e.num * (root / e.den);
                if (power > MAX_UNIVARIATE) { usable[i] = 0; break; }
                coefficient[power] += (double)value.num / (double)value.den;
                if (power > degree) degree = (int)power;
            }
            if (usable[i] && degree >= 1) {
                roots += real_roots(coefficient, degree, real + roots);
                useful = 1;
            }
        }

        /* In ordine crescente, con un inserimento alla volta. */
        for (int a = 1; a < roots; a++)
            for (int b = a; b > 0 && real[b - 1] > real[b]; b--) {
                double swap = real[b];
                real[b] = real[b - 1];
                real[b - 1] = swap;
            }

        /* I candidati per y: prima i numeri semplici, poi un numero per ogni
         * intervallo tra due radici (il più semplice: un intero se c'è, se
         * no un multiplo di 1/2, di 1/4, ...) e uno oltre ciascun estremo. */
        for (int k = 0; k < POINT_SAMPLES; k++) candidate[candidates++] = point_samples[k];
        for (int k = 0; k <= roots && roots > 0; k++) {
            double low = k > 0 ? real[k - 1] : real[0] - 2, high = k < roots ? real[k] : real[roots - 1] + 2;
            if (low < -1e12 || high > 1e12) continue;
            for (long long den = 1; den <= 1048576; den *= 2) {
                long long num = (long long)(low * (double)den);
                while ((double)num <= low * (double)den) num++;
                if ((double)num < high * (double)den) { candidate[candidates++] = frac_make(num, den); break; }
            }
        }

        /* Il primo candidato che rispetta, con un conto esatto, tutte le
         * condizioni lette. Con T = y^d e d > 1, y è una radice: positivo. */
        for (int k = 0; k < candidates && chosen < 0; k++) {
            int fine = root == 1 || candidate[k].num > 0;
            for (int i = 0; i < condition_count && fine; i++) {
                int known = 1, sign = usable[i] ? power_sum_sign(view[i], carrier, root, candidate[k], &known) : 1;
                Requirement kind = conditions[i].kind;
                fine = known && (kind == NEVER_ZERO ? sign != 0 : kind == ALWAYS_POSITIVE ? sign > 0 : sign >= 0);
            }
            if (fine) chosen = k;
        }
        if (chosen < 0) return 0;

        /* Da y a T = y^d, e da T a x. */
        Frac value = frac_int(1);
        for (long long k = 0; k < root && !failure; k++) value = frac_mul(value, candidate[chosen]);
        point_value[j] = frac_div(frac_add(value, frac_neg(shift)), slope);

        /* Il valore scelto entra nelle condizioni che restano; quelle in cui
         * non si riesce a sostituirlo non contano più. */
        for (int i = 0; i < condition_count && !failure; i++) {
            Poly next = poly_substitute(conditions[i].factor[0], x, rat_frac(point_value[j])).num;
            if (failure) { conditions[i].kind = NEVER_ZERO; next = poly_const(num_int(1)); }
            failure = NULL;
            conditions[i].factor[0] = next;
        }
        if (failure) { failure = NULL; return 0; }
    }
    return useful;
}

/* Il punto in cui l'ultima verify_instances() ha stabilito che l'enunciato
 * è definito per ogni n (13c): i primi fixed_count parametri, con i loro
 * valori. fixed_count vale -1 se non c'è, perché l'ha stabilito in altro
 * modo (13d). Le chiamate con `every` a zero non lo toccano. Lo usa il
 * certificato (13h), che lo consegna al verificatore perché lo ricontrolli. */
static int fixed_count = -1;
static int fixed_name[MAX_POINT];
static Frac fixed_value[MAX_POINT];

/* 13e. Verifica indipendente di un enunciato già dimostrato, a partire dal
 * caso base `base`. Ritorna NULL se conferma la dimostrazione, altrimenti il
 * motivo, in italiano, per cui il verdetto non va emesso.
 *
 * La dimostrazione è algebra sulle lettere: vale "dove i due membri sono
 * definiti", e non dice se quel dove esiste. ln(-x) = ln(x) passa, perché i
 * logaritmi sono trattati come ln|x|, ma non c'è un solo x in cui tutti e due
 * i membri abbiano senso. Qui si fa ciò che l'algebra non fa: si danno ai
 * parametri dei valori numerici e si calcolano davvero i due membri per
 * n = base, base + 1, ..., base + SEARCH_SPAN. Con i numeri al posto delle
 * lettere i controlli della valutazione (capitolo 11) scattano: logaritmo di
 * un numero non positivo, radice di un numero negativo, divisione per zero.
 * Poi, se `every` è diverso da zero, si decide se nello stesso punto i due
 * membri sono definiti anche per tutti gli n successivi (13c); e se non lo
 * sono, se per ogni n lo sono per tutti i valori dei parametri abbastanza
 * grandi (13d).
 *
 * Serve un punto in cui tutto è definito per ogni n. I valori provati per i
 * parametri sono pochi numeri semplici, positivi e negativi, grandi e
 * piccoli, combinati in modi diversi a ogni tentativo; se nessuno va bene,
 * un ultimo tentativo usa valori scelti guardando le condizioni di esistenza
 * (choose_point()). Si rinuncia, e il verdetto diventa NON DIMOSTRATO, in
 * quattro casi:
 *
 *   - in nessun punto provato il caso base è definito: l'enunciato sembra
 *     vuoto;
 *   - in ogni punto provato c'è un n in cui un'espressione non è definita:
 *     l'enunciato non può valere "per ogni n";
 *   - c'è un punto che i numeri non smentiscono, ma non si sa stabilire che
 *     regga per tutti gli n, o i numeri sono troppo grandi per calcolarlo;
 *   - in un punto i due membri sono numeri diversi: sarebbe un errore del
 *     programma, e la dimostrazione non va creduta.
 *
 * Un conto che si ferma per un limite del programma, come i numeri troppo
 * grandi, non dice nulla: da lì in poi quel punto non viene più calcolato,
 * senza obiezioni. Ma se si ferma già al primo valore il punto non ha
 * confermato niente, e non conta.
 *
 * `every` è zero quando si ricontrolla una formula scritta in una
 * dimostrazione (13g): lì conta solo che i numeri tornino.
 *
 * I conti fatti qui non servono dopo: atomi e memoria tornano com'erano. */
static const char *verify_instances(const Statement *statement, long long base, int every) {
    static char text[200];
    if (every) fixed_count = -1;
    Scratch mark = scratch_mark();
    const char *problem = NULL;
    long long reached = base - 1;  /* l'ultimo n fin dove un tentativo è arrivato */
    const char *why = NULL;        /* che cosa non è definito in quell'n */
    int undecided = 0;             /* 1 se un punto non è smentito, ma nemmeno confermato per ogni n */
    int far = 0;                   /* esito di defined_eventually(), 0 finché non è stato chiesto */

    /* I parametri: le lettere dell'enunciato diverse dalla variabile di
     * induzione. Pi greco è un numero, non un parametro. */
    point_count = 0;
    for (int i = 0; i < mark.atoms && point_count < MAX_POINT; i++)
        if (atoms[i].kind == ATOM_VAR && atoms[i].id != induction_var && atoms[i].id != VAR_PI && atoms[i].id != VAR_SLACK)
            point_name[point_count++] = (int)atoms[i].id;

    /* Senza parametri c'è un solo punto da provare. Con i parametri, dopo i
     * tentativi con i numeri semplici ce n'è uno con valori scelti apposta. */
    int attempts = point_count ? 4 * POINT_SAMPLES : 1, confirmed = 0;
    for (int attempt = 0; attempt <= attempts && !confirmed && !problem; attempt++) {
        if (attempt == attempts) {
            int chosen = point_count && choose_point(statement, base);
            scratch_drop(mark);
            if (!chosen) break;
        } else {
            /* Valori diversi per parametri diversi, e combinazioni diverse a
             * ogni giro dell'elenco. */
            for (int j = 0; j < point_count; j++)
                point_value[j] = point_samples[(attempt * (2 * j + 1) + (attempt / POINT_SAMPLES) * j + j) % POINT_SAMPLES];
        }

        confirmed = 1;
        for (long long c = base; c <= base + SEARCH_SPAN && confirmed && !problem; c++) {
            Num value;
            failure = NULL;
            undefined = 0;
            Rat d = difference(statement, rat_int(c));
            int limit = failure && !undefined;
            if (failure && undefined) {
                confirmed = 0;
                if (c > reached) { reached = c; why = failure; }
            } else if (limit && c == base) {
                /* Nemmeno il primo valore si è potuto calcolare: questo punto
                 * non ha confermato nulla. Prenderlo per buono farebbe
                 * passare x^100 + ln(-x) = x^100 + ln(x), dove i numeri
                 * diventano troppo grandi prima di arrivare al logaritmo. */
                confirmed = 0;
                undecided = 1;
            } else if (!failure && rat_number(d, &value) && !num_is_zero(value)) {
                snprintf(text, sizeof text, "la verifica numerica non conferma la dimostrazione: per %c = %lld i due membri sono diversi",
                         induction_var, c);
                problem = text;
            }
            scratch_drop(mark);
            if (limit) break;
        }

        /* 13c. Il punto regge per i primi n: regge per tutti? */
        if (confirmed && every && !problem) {
            long long where = base;
            const char *broken = NULL;
            failure = NULL;
            int answer = defined_for_every(statement, base, &where, &broken);
            scratch_drop(mark);
            if (answer == 1) {
                fixed_count = point_count;
                memcpy(fixed_name, point_name, sizeof fixed_name);
                memcpy(fixed_value, point_value, sizeof fixed_value);
            }

            /* 13d. Questo valore non va bene per ogni n: ma forse per ogni n
             * vanno bene tutti i valori abbastanza grandi. Lo si chiede una
             * volta sola, perché non dipende dal punto. */
            if (answer != 1 && point_count && !far) {
                far = defined_eventually(statement, base);
                scratch_drop(mark);
            }
            if (answer != 1 && far != 1) confirmed = 0;
            if (answer < 0) undecided = 1;
            if (answer == 0 && where > reached) { reached = where; why = broken; }
        }
    }
    if (!confirmed && !problem) {
        if (undecided) {
            snprintf(text, sizeof text, "non riesco a stabilire che le espressioni dell'enunciato siano definite per ogni %c", induction_var);
            problem = text;
        } else if (reached <= base && point_count) {
            problem = "non trovo valori dei parametri per cui tutte le espressioni dell'enunciato sono definite";
        } else if (why == REWRITTEN) {
            snprintf(text, sizeof text, "per %c = %lld %s", induction_var, reached, why);
            problem = text;
        } else {
            snprintf(text, sizeof text, "per %c = %lld l'enunciato non è definito: %s", induction_var, reached, why);
            problem = text;
        }
    }
    failure = NULL;
    undefined = 0;
    point_count = 0;
    return problem;
}

/* 13f. LA DIMOSTRAZIONE SCRITTA
 *
 * Il testo ripercorre ciò che il programma ha fatto, con le espressioni vere:
 *
 *   - caso base: i due membri con il numero al posto di n, e il loro valore;
 *   - ipotesi induttiva: l'enunciato per n;
 *   - passo: l'enunciato per n + 1; per ogni somma o prodotto, i termini che
 *     si aggiungono passando da n a n + 1; il valore che l'ipotesi dà alla
 *     somma ricavata; e ciò che i due membri diventano dopo la sostituzione.
 *
 * Servono due modi di scrivere un'espressione. put_node() riscrive un albero
 * com'è nell'enunciato, eventualmente con una variabile sostituita: serve per
 * "il membro sinistro per n + 1" e per "il termine con k = n + 1". put_rat()
 * scrive invece una frazione di polinomi negli atomi, cioè la forma a cui la
 * valutazione riduce ogni espressione: serve per i valori e per i risultati
 * dei conti. Un'espressione troppo lunga non viene scritta, e il testo dice
 * solo che il conto è stato fatto. */

/* Scrive il numero v in LaTeX. */
void put_frac(Frac v) {
    if (v.den == 1) proof_add("%lld", v.num);
    else proof_add("%s\\frac{%lld}{%lld}", v.num < 0 ? "-" : "", llabs(v.num), v.den);
}

/* La sostituzione in corso mentre put_node() scrive: la variabile shown_name
 * va scritta come l'espressione shown_value. Con shown_value NULL non si
 * sostituisce nulla. */
int shown_name;
const Node *shown_value;

/* Ritorna quanto strettamente il nodo tiene insieme i suoi operandi, per
 * decidere le parentesi: 1 somme e differenze, 2 somme e prodotti scritti con
 * \sum e \prod, 3 prodotti, 4 potenze e fattoriali, 5 ciò che è già un blocco
 * unico.
 *
 * Il livello 2 esiste perché un \sum prende come corpo tutto il prodotto che
 * lo segue (capitolo 9): come addendo non vuole parentesi, come fattore sì,
 * altrimenti inghiottirebbe i fattori scritti dopo. */
static int node_precedence(const Node *n) {
    switch (n->kind) {
    case N_ADD: case N_SUB: case N_NEG: return 1;
    case N_BIGOP: return 2;
    case N_MUL: return 3;
    case N_POW: return 4;
    case N_CALL: return n->op == FN_FACT ? 4 : 5;
    case N_NUM: return n->value < 0 ? 1 : 5;
    default: return 5;
    }
}

/* Scrive in LaTeX l'espressione dell'albero n, applicando la sostituzione in
 * corso. need è la precedenza minima che il contesto accetta senza
 * parentesi: un nodo che lega meno viene messo tra parentesi.
 *
 * Warning: se aggiungi un tipo di nodo o una funzione, aggiungine il caso
 * anche qui; ciò che questa funzione scrive deve rileggersi, con il parser
 * del capitolo 9, come l'espressione di partenza. */
void put_node(const Node *n, int need) {
    static const char *const call_name[] = {[FN_SIN] = "sin", [FN_COS] = "cos", [FN_TAN] = "tan", [FN_COT] = "cot",
                                            [FN_ARCTAN] = "arctan", [FN_LN] = "ln", [FN_ARCSIN] = "arcsin",
                                            [FN_ARCCOS] = "arccos", [FN_ARCCOT] = "arccot"};

    /* La variabile sostituita. Dentro l'espressione che la sostituisce non
     * si sostituisce di nuovo. */
    if (n->kind == N_VAR && shown_value && n->name == shown_name) {
        const Node *value = shown_value;
        shown_value = NULL;
        put_node(value, need);
        shown_value = value;
        return;
    }

    int wrap = node_precedence(n) < need;
    if (wrap) proof_add("\\left(");
    switch (n->kind) {
    case N_NUM:
        proof_add("%lld", n->value);
        break;
    case N_VAR:
        if (n->name == VAR_PI) proof_add("\\pi"); else proof_add("%c", n->name);
        break;
    case N_SEQ:
        proof_add("%c_{", n->name);
        put_node(n->a, 0);
        proof_add("}");
        break;
    case N_NEG:
        proof_add("-");
        put_node(n->a, 3);
        break;
    case N_ADD: case N_SUB:
        put_node(n->a, 1);
        proof_add(n->kind == N_ADD ? " + " : " - ");
        put_node(n->b, 2);
        break;
    case N_MUL: {
        /* Un numero davanti a una lettera si scrive accostato, 2n; ma non se
         * al posto della lettera va scritto un numero, perché 2 e 1
         * accostati si leggerebbero 21. */
        int replaced = shown_value && n->b->kind == N_VAR && n->b->name == shown_name;
        int juxtaposed = n->a->kind == N_NUM && n->b->kind == N_VAR && !(replaced && shown_value->kind == N_NUM);
        put_node(n->a, 3);
        if (!juxtaposed) proof_add(" \\cdot ");
        put_node(n->b, 4);
        break;
    }
    case N_DIV:
        proof_add("\\frac{");
        put_node(n->a, 0);
        proof_add("}{");
        put_node(n->b, 0);
        proof_add("}");
        break;
    case N_POW:
        /* La potenza di una funzione si scrive \cos^{2}(x), come la legge il
         * parser. */
        if (n->a->kind == N_CALL && n->a->op >= FN_SIN && n->a->op <= FN_LN) {
            proof_add("\\%s^{", call_name[n->a->op]);
            put_node(n->b, 0);
            proof_add("}\\left(");
            put_node(n->a->a, 0);
            proof_add("\\right)");
            break;
        }
        /* Una frazione come base va tra parentesi: \frac{1}{x}^{2} si
         * rilegge bene, ma a occhio sembra il quadrato del solo x. */
        if (n->a->kind == N_DIV) proof_add("\\left(");
        put_node(n->a, 5);
        if (n->a->kind == N_DIV) proof_add("\\right)");
        proof_add("^{");
        put_node(n->b, 0);
        proof_add("}");
        break;
    case N_BIGOP: {
        /* L'indice nasconde, nel corpo, una variabile con lo stesso nome. */
        const Node *kept = shown_value;
        proof_add("\\%s_{%c=", n->op ? "prod" : "sum", n->name);
        put_node(n->a, 0);
        proof_add("}^{");
        put_node(n->b, 0);
        proof_add("} ");
        if (n->name == shown_name) shown_value = NULL;
        put_node(n->c, 3);
        shown_value = kept;
        break;
    }
    case N_CALL:
        if (n->op == FN_FACT) {
            put_node(n->a, 5);
            proof_add("!");
        } else if (n->op == FN_BINOM) {
            proof_add("\\binom{");
            put_node(n->a, 0);
            proof_add("}{");
            put_node(n->b, 0);
            proof_add("}");
        } else if (n->op == FN_ROOT) {
            proof_add("\\sqrt");
            if (n->b->kind != N_NUM || n->b->value != 2) { proof_add("["); put_node(n->b, 0); proof_add("]"); }
            proof_add("{");
            put_node(n->a, 0);
            proof_add("}");
        } else if (n->op == FN_ABS) {
            proof_add("\\left|");
            put_node(n->a, 0);
            proof_add("\\right|");
        } else {
            if (n->op == FN_LOG) { proof_add("\\log_{"); put_node(n->b, 0); proof_add("}"); }
            else proof_add("\\%s", call_name[n->op]);
            proof_add("\\left(");
            put_node(n->a, 0);
            proof_add("\\right)");
        }
        break;
    case N_APPLY:
        /* Un'operazione dichiarata (9g) si scrive tra i suoi due argomenti,
         * e sempre tra parentesi, come la grammatica la vuole. */
        if (n->name >= OPERATION_NAMES) {
            proof_add("\\left(");
            put_node(n->a, 5);
            proof_add(" \\%s ", operation_symbols[n->name - OPERATION_NAMES]);
            put_node(n->b, 5);
            proof_add("\\right)");
            break;
        }
        proof_add("%c\\left(", n->name);
        put_node(n->a, 0);
        proof_add("\\right)");
        break;
    case N_DERIV:
        /* Il segno deriva tutto il term che lo segue (9d): tra parentesi,
         * non si prende i fattori scritti dopo. */
        proof_add("\\left(\\frac{d^{%lld}}{d%c^{%lld}}\\left(", n->value, n->name, n->value);
        put_node(n->a, 0);
        proof_add("\\right)\\right)");
        break;
    }
    if (wrap) proof_add("\\right)");
}

/* Ritorna l'albero dell'espressione a * variable + c, con a positivo, scritta
 * nel modo più breve: n, n + 1, 2 n - 1. */
Node *node_affine(long long a, int variable, long long c) {
    Node *n = node_new(N_VAR, NULL, NULL);
    n->name = variable;
    if (a != 1) n = node_new(N_MUL, node_num(a), n);
    if (c > 0) return node_new(N_ADD, n, node_num(c));
    if (c < 0) return node_new(N_SUB, n, node_num(-c));
    return n;
}

/* Prototipi in avanti necessari: un atomo può contenere una frazione (le
 * arcotangenti), un polinomio (le basi) o un monomio (gli esponenti), e
 * questi sono fatti di atomi. */
void put_rat(Rat r);
void put_terms(Poly p);
void put_mono(const Mono *m);

/* Diventa 1 quando put_rat() incontra una quantità che il LaTeX degli
 * enunciati non sa dire: un numero immaginario, o una potenza di e^i che non
 * sia una potenza di -1. Seni e coseni sono calcolati con gli esponenziali
 * complessi, ma in quella forma non si possono né scrivere in modo leggibile
 * né rileggere: chi chiama rinuncia a scrivere l'espressione. */
int unwritable;

/* Scrive la somma o il prodotto dell'atomo BIGOP `atom` con `shift` termini
 * in più: l'estremo superiore è dilation * n + offset + shift. Le successioni
 * del vocabolario si scrivono con il loro nome: n!, H_{n}. Un atomo è una
 * funzione di n così com'è: la sostituzione in corso non lo riguarda. */
static void put_bigop(int atom, long long shift) {
    const Atom *a = &atoms[atom];
    const Node *upper = node_affine(a->dilation, induction_var, a->offset + shift), *kept = shown_value;
    int named = bigop_library(atom);
    shown_value = NULL;
    if (named >= 0 && library[named].name == '!') {
        put_node(upper, 5);
        proof_add("!");
    } else if (named >= 0) {
        proof_add("%c_{", library[named].name);
        put_node(upper, 0);
        proof_add("}");
    } else {
        proof_add("\\%s_{%c=", a->node->op ? "prod" : "sum", a->node->name);
        put_node(a->node->a, 0);
        proof_add("}^{");
        put_node(upper, 0);
        proof_add("} ");
        put_node(a->node->c, 3);
    }
    shown_value = kept;
}

/* Scrive l'atomo elevato a exp, diverso da zero. Ogni tipo di atomo si scrive
 * come la quantità che rappresenta (vedi il capitolo 4), nel LaTeX che il
 * parser del capitolo 9 sa rileggere:
 *
 *   VAR    la lettera;
 *   BIGOP  la somma o il prodotto, tra parentesi, o il nome nel vocabolario;
 *   REC    il termine della successione, come F_{n + 1};
 *   POW    base^{esponente}: l'esponente dell'atomo e exp si moltiplicano;
 *          l'esponente 1/2 su una base presa come lettera è una radice;
 *          e^{i pi M} con M intero è (-1)^M (vedi 4g);
 *   LN     \ln del valore assoluto della base;
 *   ATAN   \arctan dell'argomento.
 *
 * Warning: se aggiungi un tipo di atomo, aggiungine il caso qui. */
void put_atom(int atom, Frac exp) {
    const Atom *a = &atoms[atom];
    int one = exp.num == 1 && exp.den == 1;
    switch (a->kind) {
    case ATOM_VAR:
        if (a->id == VAR_SLACK) unwritable = 1;
        else if (a->id == VAR_PI) proof_add("\\pi");
        else proof_add("%c", (int)a->id);
        break;
    case ATOM_REC:
        proof_add("%c_{", library[a->id].name);
        put_node(node_affine(a->dilation, induction_var, a->offset), 0);
        proof_add("}");
        break;
    case ATOM_BIGOP: {
        int named = bigop_library(atom) >= 0;
        if (!named) proof_add("\\left(");
        put_bigop(atom, 0);
        if (!named) proof_add("\\right)");
        break;
    }
    case ATOM_POW: {
        /* Le potenze di e^i: si scrive solo (-1)^M, togliendo il pi greco
         * dall'esponente. */
        if (a->base == BASE_EI) {
            if (a->pi != PI_INTEGER || !one) { unwritable = 1; return; }
            proof_add("\\left(-1\\right)^{");
            for (int i = 0, written = 0; i < a->exponent.count; i++) {
                const Factor *f = &a->exponent.factor[i];
                if (atoms[f->atom].kind == ATOM_VAR && atoms[f->atom].id == VAR_PI) continue;
                if (written++) proof_add("\\,");
                put_atom(f->atom, f->exp);
            }
            proof_add("}");
            return;
        }

        /* La base: un numero o una lettera da soli, altrimenti tra parentesi;
         * sotto radice le parentesi non servono. */
        int root = a->exponent.count == 0 && exp.num == 1 && exp.den == 2;
        const Poly *poly = a->base == BASE_POLY ? &base_polys[a->id] : NULL;
        int whole = poly && poly->count == 1 && poly->term[0].mono.count == 0 && poly->term[0].coef.im.num == 0 &&
                    poly->term[0].coef.re.den == 1 && poly->term[0].coef.re.num > 0;
        int simple = a->base == BASE_PRIME || (a->base == BASE_ATOM && atoms[a->id].kind == ATOM_VAR) || whole;
        proof_add(root ? "\\sqrt{" : simple ? "" : "\\left(");
        if (a->base == BASE_PRIME) proof_add("%lld", a->id);
        else if (a->base == BASE_ATOM) put_atom((int)a->id, frac_int(1));
        else put_terms(base_polys[a->id]);
        proof_add(root ? "}" : simple ? "" : "\\right)");
        if (root || (a->exponent.count == 0 && one)) return;

        /* L'esponente: exp per il monomio dell'atomo. */
        proof_add("^{");
        if (a->exponent.count == 0) {
            put_frac(exp);
        } else {
            if (exp.num == -1 && exp.den == 1) proof_add("-");
            else if (!one) { put_frac(exp); proof_add("\\,"); }
            put_mono(&a->exponent);
        }
        proof_add("}");
        return;
    }
    case ATOM_LN:
        /* Anche l'argomento numerico va chiuso: in un monomio \ln 3\,e^x
         * si rileggerebbe come ln(3 e^x), non ln(3) per e^x. Le parentesi
         * esterne, quando exp non e 1, separano invece (ln 3)^exp da
         * ln(3^exp). Nessuno dei due confini puo essere lasciato implicito. */
        proof_add(one ? "\\ln " : "\\left(\\ln ");
        if (a->base == BASE_PRIME) {
            proof_add("\\left(%lld\\right)", a->id);
        } else {
            proof_add("\\left|");
            if (a->base == BASE_ATOM) put_atom((int)a->id, frac_int(1)); else put_terms(base_polys[a->id]);
            proof_add("\\right|");
        }
        if (!one) proof_add("\\right)");
        break;
    case ATOM_ATAN:
        proof_add("\\arctan\\left(");
        put_rat(atan_args[a->id]);
        proof_add("\\right)");
        break;
    }
    if (!one) { proof_add("^{"); put_frac(exp); proof_add("}"); }
}

/* Diverso da zero mentre le potenze con esponente k/2 vanno scritte come
 * potenze intere di una radice quadrata, \sqrt{u}^{k}, invece che u^{k/2}. Le
 * due scritture valgono lo stesso numero, perché u, base di una radice, non
 * è negativo. Serve al capitolo 25: la tabella dei segni (18p) legge le
 * radici quadrate ma non gli esponenti frazionari. */
int surd_powers;

/* Scrive il monomio m: i suoi fattori, separati da uno spazio sottile. */
void put_mono(const Mono *m) {
    for (int i = 0; i < m->count; i++) {
        const Atom *a = &atoms[m->factor[i].atom];
        Frac e = m->factor[i].exp;
        if (i) proof_add("\\,");

        /* Le potenze di e^i non sono radici di numeri reali: restano a
         * put_atom(), che le dichiara non scrivibili. */
        if (!surd_powers || e.den != 2 || (a->kind == ATOM_POW && a->base == BASE_EI)) {
            put_atom(m->factor[i].atom, e);
            continue;
        }

        /* Di una base presa come lettera put_atom() sa già scrivere la
         * radice; degli altri atomi la si scrive qui. */
        if (a->kind == ATOM_POW && a->exponent.count == 0) {
            put_atom(m->factor[i].atom, (Frac){1, 2});
        } else {
            proof_add("\\sqrt{");
            put_atom(m->factor[i].atom, frac_int(1));
            proof_add("}");
        }
        if (e.num != 1) proof_add("^{%lld}", e.num);
    }
}

/* Scrive il polinomio negli atomi p, un termine dopo l'altro: segno, valore
 * assoluto del coefficiente (taciuto se è 1 davanti a degli atomi), atomi. */
void put_terms(Poly p) {
    if (p.count == 0) { proof_add("0"); return; }
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        if (t->coef.im.num != 0) { unwritable = 1; return; }
        Frac size = t->coef.re;
        int negative = size.num < 0, bare = t->mono.count == 0, unit;
        if (negative) size = frac_neg(size);
        unit = size.num == 1 && size.den == 1;
        proof_add("%s", i ? (negative ? " - " : " + ") : (negative ? "-" : ""));
        if (!unit || bare) put_frac(size);
        if (bare) continue;

        /* Tra il coefficiente e una potenza di un numero ci vuole il punto:
         * 2 e 3^n accostati si leggerebbero 23^n. */
        const Factor *first = &t->mono.factor[0];
        const Atom *a = &atoms[first->atom];
        int root = a->exponent.count == 0 && first->exp.num == 1 && first->exp.den == 2;
        int digit = a->kind == ATOM_POW && a->base == BASE_PRIME && !root;
        if (!unit) proof_add(digit ? " \\cdot " : "\\,");
        put_mono(&t->mono);
    }
}

/* Scrive la frazione di polinomi r; solo il numeratore se il denominatore è
 * 1. Come per put_bigop(), la sostituzione in corso non riguarda gli atomi. */
void put_rat(Rat r) {
    const Node *kept = shown_value;
    shown_value = NULL;
    if (poly_is_one(r.den)) {
        put_terms(r.num);
    } else {
        proof_add("\\frac{");
        put_terms(r.num);
        proof_add("}{");
        put_terms(r.den);
        proof_add("}");
    }
    shown_value = kept;
}

/* Toglie dal testo della dimostrazione ciò che segue i primi length
 * caratteri. */
void proof_cut(size_t length) {
    proof_length = length;
    proof_text[length] = 0;
}

/* Scrive il membro `side` dell'enunciato con la variabile di induzione
 * sostituita da value (NULL: così com'è) e ritorna il pezzo scritto. */
Span put_side(const Node *side, const Node *value) {
    Span span = {proof_length, 0};
    shown_name = induction_var;
    shown_value = value;
    put_node(side, 0);
    shown_value = NULL;
    span.to = proof_length;
    return span;
}

/* Scrive prefix e poi il valore r, e ritorna 1 con il pezzo del valore in
 * *span. Se r non si può scrivere, perché troppo lungo, o non reale, o
 * perché un conto è fallito, non scrive nulla e ritorna 0. */
int put_value(const char *prefix, Rat r, Span *span) {
    size_t start = proof_length;
    if (failure || r.num.count + r.den.count > 14) return 0;
    proof_add("%s", prefix);
    span->from = proof_length;
    unwritable = 0;
    put_rat(r);
    span->to = proof_length;
    if (!unwritable) return 1;
    proof_cut(start);
    return 0;
}

/* 13g. IL CONTROLLO DELLE FORMULE SCRITTE
 *
 * Ritorna 1 se l'uguaglianza tra le due formule scritte nei pezzi a e b della
 * dimostrazione è confermata per un'altra strada: le due formule vengono
 * rilette dal testo con il parser degli enunciati, come se le avesse scritte
 * l'utente, e l'uguaglianza passa per la verifica numerica 13e a partire da
 * n = base.
 *
 * Chi scrive la formula e chi la controlla non hanno nulla in comune: la
 * scrittura parte dagli alberi e dai polinomi negli atomi, il controllo dai
 * caratteri del testo e dai numeri. Un errore nel modo di scrivere (una
 * parentesi mancante, una sostituzione fatta male, un segno) cambia il valore
 * di ciò che si rilegge, e qui si vede. */
int reread_equal(Span a, Span b, long long base) {
    char text[MAX_FORMULA];
    Statement statement;
    size_t kept = arena_used;
    int length = snprintf(text, sizeof text, "%.*s = %.*s", (int)(a.to - a.from), proof_text + a.from,
                          (int)(b.to - b.from), proof_text + b.from);
    int holds = length > 0 && (size_t)length < sizeof text && parse_statement(text, &statement) && !failure &&
                verify_instances(&statement, base, 0) == NULL;
    arena_used = kept;
    failure = NULL;
    return holds;
}

/* Ritorna 1 se i due pezzi del testo contengono gli stessi caratteri. */
static int span_same(Span a, Span b) {
    return a.to - a.from == b.to - b.from && memcmp(proof_text + a.from, proof_text + b.from, a.to - a.from) == 0;
}

/* Ritorna il valore del membro `side` dell'enunciato con la variabile di
 * induzione legata a n. */
Rat side_value(const Node *side, Rat n) {
    env_count = 0;
    library_depth = 0;
    env_push(induction_var, n);
    Rat value = eval(side);
    env_count = 0;
    return value;
}

/* Scrive, un \item per ciascuno, i termini che ogni somma o prodotto
 * dell'enunciato guadagna passando da n a n + 1: gli indici da
 * dilation * n + offset + 1 a dilation * (n + 1) + offset. Ogni uguaglianza
 * scritta viene riletta (13g) a partire da n = base: ritorna 1 se reggono
 * tutte. */
int put_new_terms(long long base) {
    int sound = 1;
    for (int x = 0; x < atom_count; x++) {
        const Atom *a = &atoms[x];
        if (a->kind != ATOM_BIGOP) continue;
        Span longer = {proof_length + strlen("\\item $"), 0}, split;
        proof_add("\\item $");
        put_bigop(x, a->dilation);
        longer.to = proof_length;
        proof_add(" = ");
        split.from = proof_length;

        /* Un \prod prende come corpo tutti i fattori che lo seguono
         * (capitolo 9): senza parentesi inghiottirebbe quelli nuovi. */
        int wrap = a->node->op && bigop_library(x) < 0;
        if (wrap) proof_add("\\left(");
        put_bigop(x, 0);
        if (wrap) proof_add("\\right)");
        for (long long j = 1; j <= a->dilation; j++) {
            proof_add(a->node->op ? " \\cdot " : " + ");
            shown_name = a->node->name;
            shown_value = node_affine(a->dilation, induction_var, a->offset + j);
            put_node(a->node->c, a->node->op ? 4 : 2);
            shown_value = NULL;
        }
        split.to = proof_length;
        proof_add("$.\n");
        sound &= reread_equal(longer, split, base);
    }
    return sound;
}

/* Scrive la dimostrazione per induzione dell'enunciato, già verificata: caso
 * base `base`, d = D(n), e `used` l'atomo ricavato dall'ipotesi nel passo
 * (-1 se non è servita), come li ha lasciati step_holds().
 *
 * Ogni formula scritta viene riletta e ricontrollata con reread_equal(). Se
 * anche una sola non regge, tutto il testo è sostituito da uno schema senza
 * formule e unjustified_steps sale: il verdetto resta, perché non dipende dal
 * testo, ma un passaggio non confermato non va stampato.
 *
 * I conti rifatti qui servono solo a mostrare le espressioni: un loro errore,
 * come un'espressione fuori dai limiti, toglie una frase dal testo ma non
 * tocca il verdetto, quindi `failure` torna com'era.
 *
 * Il testo si aggiunge a quello già scritto. Con nested diverso da zero è un
 * passo di una dimostrazione più grande (regola 18n): un \item con i suoi
 * sotto-passi, senza l'intestazione e senza il quadratino finale. */
static void put_induction_proof(const Statement *statement, long long base, Rat d, int used, int nested) {
    int variable = induction_var, sound = 1, valued = 1;
    const char *saved = failure;
    size_t opening = proof_length;
    const Node *side[2] = {statement->lhs, statement->rhs}, *successor = node_affine(1, variable, 1);
    Rat next = rat_add(rat_atom(atom_var(variable)), rat_int(1), 0);
    Span text[2], value[2];

    /* Caso base: i due membri con il numero al posto di n, e il loro valore.
     * Un membro che è già un numero non ha bisogno di "= valore". */
    proof_add(nested ? "\\item By induction on $%c$.\n" : "\\textbf{Proof.} By induction on $%c$.\n", variable);
    proof_add("\\begin{itemize}\n\\item \\emph{Base case}, $%c = %lld$. ", variable, base);
    for (int s = 0; s < 2; s++) {
        Rat low = side_value(side[s], rat_int(base));
        proof_add(s ? " and the right-hand side is $" : "The left-hand side is $");
        text[s] = put_side(side[s], node_num(base));
        if (side[s]->kind == N_NUM || (side[s]->kind == N_VAR && side[s]->name == variable)) value[s] = text[s];
        else if (put_value(" = ", low, &value[s])) sound &= reread_equal(text[s], value[s], base);
        else valued = 0;
        proof_add("$");
    }
    sound &= reread_equal(text[0], text[1], base);
    proof_add(valued && span_same(value[0], value[1]) ? ": the two values are equal.\n"
                  : ": the two sides are equal, because their difference reduces to $0$ by exact algebra.\n");

    /* 11n. La regola con cui sono state calcolate le somme che hanno n nel
     * coefficiente binomiale: va detta, perché da lì in poi quelle somme
     * compaiono solo con la loro forma chiusa. */
    if (binomial_used)
        proof_add("\\item \\emph{Binomial theorem}. For a general $%c$ a sum whose term is $\\binom{N}{k}$ times powers with $k$ in the exponent "
                  "is computed in closed form: its term is written as a sum of terms $c\\,y^{k}$, with $c$ and $y$ free of $k$, and "
                  "$\\sum_{k=0}^{N}\\binom{N}{k}y^{k} = (1 + y)^{N}$; when only the even or the odd $k$ appear, "
                  "$\\sum_{k}\\binom{N}{2k}y^{2k} = \\frac{(1 + y)^{N} + (1 - y)^{N}}{2}$ and "
                  "$\\sum_{k}\\binom{N}{2k+1}y^{2k+1} = \\frac{(1 + y)^{N} - (1 - y)^{N}}{2}$. "
                  "In the base case the sum is written out term by term instead.\n", variable);

    /* I due membri per n + 1, come li ha calcolati il passo induttivo. */
    Rat up[2] = {side_value(side[0], next), side_value(side[1], next)};

    if (used < 0) {
        /* Nessuna somma da ricavare: i due membri coincidono per ogni n. */
        proof_add("\\item \\emph{Inductive step}. Here the inductive hypothesis is not needed. For $%c + 1$ the statement is $", variable);
        text[0] = put_side(side[0], successor);
        proof_add(" = ");
        text[1] = put_side(side[1], successor);
        proof_add("$");
        sound &= reread_equal(text[0], text[1], base);
        if (!failure && rat_add(up[0], up[1], 1).num.count == 0 && put_value(", and written out both sides are $", up[0], &value[0])) {
            proof_add("$.\n");
            sound &= reread_equal(text[0], value[0], base) & reread_equal(text[1], value[0], base);
        } else {
            proof_add(", and the difference of the two sides reduces to $0$ by exact algebra.\n");
        }
    } else {
        /* L'ipotesi, e ciò che va dimostrato. */
        proof_add("\\item \\emph{Inductive hypothesis}. Assume the statement for some $%c \\ge %lld$: $", variable, base);
        put_side(side[0], NULL);
        proof_add(" = ");
        put_side(side[1], NULL);
        proof_add("$.\n\\item \\emph{Inductive step}. We prove the statement for $%c + 1$: $", variable);
        text[0] = put_side(side[0], successor);
        proof_add(" = ");
        text[1] = put_side(side[1], successor);
        proof_add("$.\n\\begin{itemize}\n");
        sound &= reread_equal(text[0], text[1], base);

        /* Seni e coseni sono calcolati come esponenziali complessi (capitolo
         * 11): il testo lo dice, perché in quella forma i risultati dei conti
         * non vengono scritti. */
        for (int x = 0, told = 0; x < atom_count && !told; x++)
            if (atoms[x].kind == ATOM_POW && atoms[x].base == BASE_EI && atoms[x].pi == PI_NONE) {
                proof_add("\\item Sines and cosines are computed as complex exponentials, $\\cos\\theta = \\frac{e^{i\\theta} + "
                          "e^{-i\\theta}}{2}$ and $\\sin\\theta = \\frac{e^{i\\theta} - e^{-i\\theta}}{2i}$; expressions in "
                          "that form are not written out below.\n");
                told = 1;
            }

        /* I termini che ogni somma o prodotto guadagna passando a n + 1. */
        sound &= put_new_terms(base);

        /* Il valore che l'ipotesi dà all'atomo ricavato: da A x + B = 0. */
        Poly hypothesis[2];
        Rat solved = rat_int(0);
        int split = poly_split(d.num, used, hypothesis, 1) == 1;
        if (split) solved = rat_make(poly_add(poly_const(num_int(0)), hypothesis[0], 1), hypothesis[1]);
        Span atom = {proof_length + strlen("\\item By the inductive hypothesis, $"), 0};
        size_t start = proof_length;
        proof_add("\\item By the inductive hypothesis, $");
        put_bigop(used, 0);
        atom.to = proof_length;
        if (split && put_value(" = ", solved, &value[0])) {
            proof_add("$.\n");
            sound &= reread_equal(atom, value[0], base);
        } else {
            proof_cut(start);
            proof_add("\\item The inductive hypothesis gives the value of $");
            put_bigop(used, 0);
            proof_add("$.\n");
        }

        /* Ciò che i due membri diventano con quel valore al posto dell'atomo. */
        for (int s = 0; s < 2 && split && !failure; s++)
            up[s] = rat_div(poly_substitute(up[s].num, used, solved), poly_substitute(up[s].den, used, solved));
        char opening[112];
        snprintf(opening, sizeof opening, "\\item With these replacements, the left-hand side for $%c + 1$ becomes $", variable);
        start = proof_length;
        int shown = split && put_value(opening, up[0], &value[0]) && put_value("$ and the right-hand side becomes $", up[1], &value[1]);
        if (shown && span_same(value[0], value[1])) {
            /* Lo stesso testo due volte: lo si dice una volta sola. */
            proof_cut(start);
            snprintf(opening, sizeof opening, "\\item With these replacements, both sides of the statement for $%c + 1$ become $", variable);
            put_value(opening, up[0], &value[0]);
            proof_add("$.\n");
            sound &= reread_equal(text[0], value[0], base) & reread_equal(text[1], value[0], base);
        } else if (shown) {
            proof_add("$. They are equal: their difference, written as one fraction, has numerator $0$.\n");
            sound &= reread_equal(text[0], value[0], base) & reread_equal(text[1], value[1], base);
        } else {
            proof_cut(start);
            proof_add("\\item With these replacements, the difference of the two sides for $%c + 1$ reduces to $0$ by exact algebra.\n", variable);
        }
        proof_add("\\end{itemize}\n");
    }
    proof_add(nested ? "\\end{itemize}\n" : "\\end{itemize}\n$\\Box$");

    /* Un passaggio non confermato: resta solo lo schema, senza formule. */
    if (!sound || proof_length >= PROOF_BYTES - 1) {
        if (!sound) unjustified_steps++;
        proof_cut(opening);
        proof_add(nested ? "\\item " : "\\textbf{Proof.} ");
        proof_add("By induction on $%c$: the base case $%c = %lld$ and the inductive step were both "
                  "checked by exact algebra on the difference of the two sides.%s", variable, variable, base, nested ? "\n" : " $\\Box$");
    }
    failure = saved;
}

/* 13h. IL CERTIFICATO
 *
 * I controlli fatti fin qui sono tutti del motore: stessa aritmetica, stesso
 * modo di leggere le formule. L'ultimo è di un altro programma. Il motore
 * scrive un certificato, cioè l'enunciato, il caso base e un "fattore" W per
 * cui D(n+1) = W D(n), e checker.c lo ricontrolla con i suoi polinomi. Che
 * cosa dimostra un certificato accettato è scritto in testa a checker.c:
 * che i due membri sono uguali dove sono definiti e, se il verificatore sa
 * ricontrollarlo, che lo sono per ogni n (vedi "La definizione", più sotto).
 *
 * Il fattore. L'ipotesi induttiva è A X + B = 0, e il numeratore di D(n+1) è
 * un polinomio in X, P(X) = C0 + C1 X + ... + Cd X^d. Il passo induttivo
 * (13b) ha controllato che A^d P(-B/A) = 0. Per il teorema del resto vuol
 * dire che A X + B divide A^d P(X):
 *
 *     A^d P(X) = Q(X) (A X + B).
 *
 * Q si trova con la regola di Ruffini. Con Y = A X, A^d P(X) è il polinomio
 * in Y di coefficienti c_j = C_j A^{d-j}, da dividere per Y + B:
 *
 *     s_{d-1} = c_d,    s_{j-1} = c_j - B s_j,    Q = s_0 + s_1 Y + ... + s_{d-1} Y^{d-1},
 *
 * e ciò che avanza, c_0 - B s_0, è proprio la quantità che 13b ha trovato
 * nulla. Con D(n) = (A X + B)/D0 e D(n+1) = P(X)/D1 si ottiene
 *
 *     D(n+1) = W D(n),    W = Q D0 / (A^d D1).
 *
 * Se D(n+1) è zero senza bisogno dell'ipotesi, W = 0.
 *
 * Un divisore di W che non è un divisore dell'enunciato. Quando A dipende
 * solo dai parametri (il secondo caso di 13b) può restare a denominatore di
 * W. Il verificatore allora respinge, a meno che il certificato dichiari A
 * tra le espressioni "generic": il teorema certificato vale dove A non è
 * zero, e l'estensione agli altri valori dei parametri resta l'argomento di
 * 13b, che il certificato non copre. Si prova prima senza.
 *
 * La definizione. 13c ha stabilito che in un certo punto dei parametri
 * l'enunciato è definito per ogni n; verify_instances() lascia quel punto in
 * fixed_name[] e fixed_value[]. Il certificato lo porta al verificatore con
 * la voce "defined", e il verificatore ricontrolla con le sue regole che
 * nessun divisore si annulli (capitolo 9 di checker.c). Le risposte sono tre
 * e contano tutte: accettato, e allora il certificato dice anche questo;
 * respinto, cioè c'è un n in cui l'enunciato non è definito e 13c ha
 * sbagliato; non controllabile, e allora si torna al certificato della sola
 * uguaglianza.
 *
 * I logaritmi. Il motore li calcola scomponendo l'argomento in fattori
 * (capitolo 11), e ogni fattore è la base di un atomo LN. Il verificatore fa
 * lo stesso conto per conto suo, ma non cerca i fattori: glieli suggerisce
 * il certificato, con una voce "brick" per ogni base, e lui li prova con una
 * divisione. Un suggerimento sbagliato non divide nulla, quindi non può far
 * accettare il falso.
 *
 * La notazione dei certificati ha meno parole di quella degli enunciati:
 * niente radici, seni, arcotangenti. Quando l'enunciato o il fattore
 * contengono qualcosa che non sa dire, il certificato non c'è, e il verdetto
 * lo dichiara.
 */

/* Il certificato dell'enunciato in corso, nella notazione di checker.c. */
static char certificate_initial[CERTIFICATE_BYTES];
char *certificate_text = certificate_initial;
size_t certificate_length, certificate_capacity = CERTIFICATE_BYTES;

/* Diventa 1 quando il certificato in corso non si può scrivere: una quantità
 * che la notazione non ha, o memoria insufficiente per il testo dinamico. */
int certificate_broken;

/* Le successioni del vocabolario nominate nel certificato in corso: il bit i
 * è la riga i di library[]. Vanno definite nel certificato stesso. */
unsigned certificate_sequences;
_Static_assert(LIBRARY_COUNT <= 32, "certificate_sequences ha un bit per ogni riga del vocabolario");

/* Perché l'ultimo certificato chiesto a certify() non c'è o non vale, in
 * italiano. Resta valido fino alla chiamata successiva. */
char certificate_problem[256];

/* 1 mentre si scrive il certificato di una tabella dei segni (18p-15): solo
 * allora il valore assoluto e la radice quadrata hanno una parola, (abs a) e
 * (sqrt a), che il verificatore conosce nel suo capitolo 12. In un
 * certificato di induzione resterebbero parole sconosciute: lì il
 * certificato manca, e il verdetto dice perché. */
int cert_signs;

/* Diverso da zero mentre si scrive il certificato di una derivata, di una
 * primitiva o di un integrale (27m, 30cert): è il nome della variabile reale, e
 * allora hanno una parola le funzioni che il verificatore conosce nel suo
 * capitolo 13: (exp a) per e^a, (sin a), (cos a), (atan a), (root m a),
 * (pi). La lettera e, se non è la variabile, è il numero di Nepero, (exp 1),
 * come nel capitolo 27. */
int cert_real;

/* Aggiunge un pezzo al certificato, con la sintassi di printf. */
void cert_add(const char *format, ...) {
    if (certificate_broken) return;
    va_list arguments;
    va_start(arguments, format);
    va_list retry; va_copy(retry, arguments);
    int written = vsnprintf(certificate_text + certificate_length, certificate_capacity - certificate_length, format, arguments);
    if (written < 0 || (size_t)written > (size_t)-1 - certificate_length - 1) certificate_broken = 1;
    else {
        size_t need = certificate_length + (size_t)written + 1;
        if (need > certificate_capacity) {
            if (!text_reserve(&certificate_text, &certificate_capacity, certificate_initial, need)) certificate_broken = 1;
            else vsnprintf(certificate_text + certificate_length, certificate_capacity - certificate_length, format, retry);
        }
        if (!certificate_broken) certificate_length += (size_t)written;
    }
    va_end(retry);
    va_end(arguments);
}

/* Scrive una lettera dell'enunciato. \pi e la lettera ausiliaria di
 * body_is_positive() non sono parametri: la notazione non li ha. */
void cert_letter(long long name) {
    if (name < 128 && isalpha((int)name)) cert_add("%c", (int)name);
    else certificate_broken = 1;
}

void cert_node(const Node *n);

/* Scrive "(word a)" oppure, se b non è NULL, "(word a b)". */
static void cert_call(const char *word, const Node *a, const Node *b) {
    cert_add("(%s ", word);
    cert_node(a);
    if (b) {
        cert_add(" ");
        cert_node(b);
    }
    cert_add(")");
}

/* Scrive il termine di indice index della riga `entry` del vocabolario. Il
 * fattoriale è una parola della notazione; le altre successioni si nominano,
 * e certify() ne aggiunge la definizione.
 *
 * Warning: "(fact a)" è per il verificatore il prodotto degli interi da 1 ad
 * a. Se cambi la riga '!' del vocabolario, il certificato non dice più ciò
 * che il motore ha dimostrato: va cambiato anche qui. */
static void cert_term(int entry, const Node *index) {
    if (library[entry].name == '!') {
        cert_call("fact", index, NULL);
        return;
    }
    certificate_sequences |= 1u << entry;
    cert_add("(seq %c ", library[entry].name);
    cert_node(index);
    cert_add(")");
}

/* Scrive la somma o il prodotto del nodo node, con upper al posto del suo
 * estremo superiore. */
static void cert_bigop(const Node *node, const Node *upper) {
    cert_add("(%s ", node->op ? "prod" : "sum");
    cert_letter(node->name);
    cert_add(" ");
    cert_node(node->a);
    cert_add(" ");
    cert_node(upper);
    cert_add(" ");
    cert_node(node->c);
    cert_add(")");
}

/* Scrive l'albero n nella notazione dei certificati: l'operatore davanti, e
 * tutte le parentesi.
 *
 * Warning: se aggiungi un tipo di nodo o una funzione, decidi qui se la
 * notazione dei certificati lo sa dire; altrimenti resta senza certificato. */
void cert_node(const Node *n) {
    static const char *const binary[] = {[N_ADD] = "+", [N_SUB] = "-", [N_MUL] = "*", [N_DIV] = "/", [N_POW] = "^"};
    switch (n->kind) {
    case N_NUM:
        cert_add("%lld", n->value);
        return;
    case N_VAR:
        if (cert_real && n->name == VAR_PI) cert_add("(pi)");
        else if (cert_real && n->name == 'e' && cert_real != 'e') cert_add("(exp 1)");
        else cert_letter(n->name);
        return;
    case N_SEQ:
        for (int i = 0; i < LIBRARY_COUNT; i++)
            if (library[i].name == n->name) { cert_term(i, n->a); return; }
        certificate_broken = 1;
        return;
    case N_NEG:
        cert_call("neg", n->a, NULL);
        return;
    case N_BIGOP:
        cert_bigop(n, n->b);
        return;
    case N_CALL:
        if (n->op == FN_FACT) {
            cert_call("fact", n->a, NULL);
        } else if (n->op == FN_BINOM) {
            cert_call("binom", n->a, n->b);
        } else if ((cert_signs || cert_real) && n->op == FN_ABS) {
            /* Nel capitolo 13 di checker.c il valore assoluto si calcola solo
             * dentro l'argomento di un logaritmo. */
            cert_call("abs", n->a, NULL);
        } else if (cert_signs && n->op == FN_ROOT && n->b->kind == N_NUM && n->b->value == 2) {
            cert_call("sqrt", n->a, NULL);
        } else if (cert_real && n->op == FN_ROOT && n->b->kind == N_NUM && n->b->value >= 2) {
            cert_add("(root %lld ", n->b->value);
            cert_node(n->a);
            cert_add(")");
        } else if (cert_real && (n->op == FN_SIN || n->op == FN_COS || n->op == FN_ARCTAN)) {
            cert_call(n->op == FN_SIN ? "sin" : n->op == FN_COS ? "cos" : "atan", n->a, NULL);
        } else if (cert_real && (n->op == FN_TAN || n->op == FN_COT)) {
            /* tan u = sin u / cos u, cot u = cos u / sin u: definite dove lo
             * sono loro, dove il denominatore non è zero. */
            cert_add("(/ ");
            cert_call(n->op == FN_TAN ? "sin" : "cos", n->a, NULL);
            cert_add(" ");
            cert_call(n->op == FN_TAN ? "cos" : "sin", n->a, NULL);
            cert_add(")");
        } else if (cert_real && n->op == FN_ARCCOT) {
            /* L'arcocotangente a valori in (0, pi) è pi/2 - arctan u. */
            cert_add("(- (/ (pi) 2) ");
            cert_call("atan", n->a, NULL);
            cert_add(")");
        } else if (n->op == FN_LN || (n->op == FN_LOG && n->b)) {
            /* Il logaritmo di un valore assoluto ha una parola sua, perché
             * è definito anche dove l'argomento è negativo (vedi
             * eval_call()). Il logaritmo in base b è ln a / ln b. */
            int absolute = n->a->kind == N_CALL && n->a->op == FN_ABS;
            if (n->op == FN_LOG) cert_add("(/ ");
            cert_call(absolute ? "lnabs" : "ln", absolute ? n->a->a : n->a, NULL);
            if (n->op == FN_LOG) {
                cert_add(" ");
                cert_call("ln", n->b, NULL);
                cert_add(")");
            }
        } else {
            certificate_broken = 1;
        }
        return;
    case N_APPLY: case N_DERIV:
        certificate_broken = 1;
        return;
    default:
        if (cert_real && n->kind == N_POW && n->a->kind == N_VAR && n->a->name == 'e' && cert_real != 'e') cert_call("exp", n->b, NULL);
        else cert_call(binary[n->kind], n->a, n->b);
    }
}

static void cert_poly(Poly p);

static void cert_atom(int atom);

/* Ritorna 1 se la base dell'atomo LN a si può suggerire al verificatore come
 * fattore degli argomenti dei logaritmi (una voce "brick", 8g in checker.c).
 * Un numero primo no: il verificatore i numeri li scompone da sé. Un
 * polinomio con un esponente negativo, come x^{-4} + 1, nemmeno: per il
 * verificatore è una frazione, e una voce brick che non è un polinomio gli
 * fa respingere tutto il certificato, non solo ignorare il suggerimento
 * (la derivata di \ln(x^{-4} + 1) restava senza verdetto per questo). */
int brick_fits(const Atom *a) {
    if (a->kind != ATOM_LN || a->base == BASE_PRIME) return 0;
    if (a->base != BASE_POLY) return 1;
    Poly p = base_polys[a->id];
    for (int i = 0; i < p.count; i++)
        for (int f = 0; f < p.term[i].mono.count; f++)
            if (p.term[i].mono.factor[f].exp.num < 0) return 0;
    return 1;
}

/* Scrive la base di un atomo POW o LN che non sia e^i: un numero primo, un
 * altro atomo, o un polinomio. */
void cert_base(const Atom *a) {
    if (a->base == BASE_PRIME) cert_add("%lld", a->id);
    else if (a->base == BASE_ATOM) cert_atom((int)a->id);
    else cert_poly(base_polys[a->id]);
}

/* Scrive l'atomo `atom` come la quantità che rappresenta (capitolo 4).
 *
 *   VAR    la lettera;
 *   BIGOP  la somma o il prodotto fino al suo estremo, o il termine della
 *          successione del vocabolario di cui è la definizione;
 *   REC    il termine della successione;
 *   POW    base^M; e^{i pi M} con M intero è (-1)^M (vedi 4g);
 *   LN     il logaritmo del valore assoluto della base.
 *
 * Arcotangenti e le altre potenze di e^i (seni e coseni) non hanno una
 * scrittura.
 *
 * Warning: se aggiungi un tipo di atomo, aggiungine il caso qui. */
static void cert_atom(int atom) {
    const Atom *a = &atoms[atom];
    switch (a->kind) {
    case ATOM_VAR:
        cert_letter(a->id);
        return;
    case ATOM_REC:
        cert_term((int)a->id, node_affine(a->dilation, induction_var, a->offset));
        return;
    case ATOM_BIGOP: {
        const Node *upper = node_affine(a->dilation, induction_var, a->offset);
        int named = bigop_library(atom);
        if (named >= 0) cert_term(named, upper); else cert_bigop(a->node, upper);
        return;
    }
    case ATOM_POW: {
        /* L'esponente; per (-1)^M è quello dell'atomo senza il pi greco. */
        Mono exponent = a->exponent;
        if (a->base == BASE_EI) {
            if (a->pi != PI_INTEGER) { certificate_broken = 1; return; }
            exponent = mono_with_exponent(&exponent, atom_var(VAR_PI), frac_int(0));
        }

        /* La base, da sola se l'atomo è la base presa come lettera. */
        if (exponent.count) cert_add("(^ ");
        if (a->base == BASE_EI) cert_add("-1"); else cert_base(a);
        if (!exponent.count) return;
        cert_add(" ");
        cert_poly(poly_term((Term){num_int(1), exponent}));
        cert_add(")");
        return;
    }
    case ATOM_LN:
        cert_add("(lnabs ");
        cert_base(a);
        cert_add(")");
        return;
    default:
        certificate_broken = 1;
    }
}

/* Scrive il numero razionale c. */
void cert_frac(Frac c) {
    if (c.den == 1) cert_add("%lld", c.num);
    else cert_add("(/ %lld %lld)", c.num, c.den);
}

/* Scrive il polinomio negli atomi p: la somma dei suoi termini, ciascuno il
 * coefficiente per i suoi atomi elevati ai loro esponenti. Un coefficiente
 * immaginario o un esponente non intero (una radice) non hanno scrittura. */
static void cert_poly(Poly p) {
    if (p.count == 0) cert_add("0");
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        Frac c = t->coef.re;
        if (t->coef.im.num != 0) certificate_broken = 1;

        /* Somme e prodotti hanno due operandi: "(+ primo (+ secondo ...))",
         * "(* (* primo secondo) terzo)". Il coefficiente 1 davanti a degli
         * atomi si tace; `shown` conta i fattori già scritti. */
        int shown = c.num != c.den || t->mono.count == 0;
        if (i + 1 < p.count) cert_add("(+ ");
        for (int j = 1; j < shown + t->mono.count; j++) cert_add("(* ");
        if (shown) cert_frac(c);
        for (int j = 0; j < t->mono.count; j++) {
            Frac e = t->mono.factor[j].exp;
            if (e.den != 1) certificate_broken = 1;
            if (shown) cert_add(" ");
            if (e.num != 1) cert_add("(^ ");
            cert_atom(t->mono.factor[j].atom);
            if (e.num != 1) cert_add(" %lld)", e.num);
            if (shown++) cert_add(")");
        }
        if (i + 1 < p.count) cert_add(" ");
    }
    for (int i = 1; i < p.count; i++) cert_add(")");
}

/* Scrive in certificate_text il certificato dell'enunciato statement con
 * caso base `base` e fattore top/bottom. Se generic non è NULL dichiara
 * quell'espressione dei parametri diversa da zero; se defined è diverso da
 * zero aggiunge la voce "defined" con il punto di 13c. Alla fine
 * certificate_broken dice se il testo è da buttare. */
static void write_certificate(const Statement *statement, long long base, Poly top, Poly bottom, const Poly *generic, int defined) {
    /* Le voci: variabile, caso base, enunciato, fattore. */
    certificate_length = 0;
    certificate_broken = 0;
    certificate_sequences = 0;
    cert_add("certificate induction\nvariable %c\nbase %lld\nstatement (= ", induction_var, base);
    cert_node(statement->lhs);
    cert_add(" ");
    cert_node(statement->rhs);
    cert_add(poly_is_one(bottom) ? ")\nfactor " : ")\nfactor (/ ");
    cert_poly(top);
    if (!poly_is_one(bottom)) {
        cert_add(" ");
        cert_poly(bottom);
        cert_add(")");
    }
    if (generic) {
        cert_add("\ngeneric ");
        cert_poly(*generic);
    }

    /* I fattori in cui il motore ha scomposto gli argomenti dei logaritmi:
     * le basi dei suoi atomi LN. Il verificatore li prova con una divisione
     * (vedi 8g in checker.c), quindi uno in più non fa danno. */
    for (int i = 0, written = 0; i < atom_count && written < MAX_BRICKS; i++) {
        if (!brick_fits(&atoms[i])) continue;
        cert_add("\nbrick ");
        cert_base(&atoms[i]);
        written++;
    }
    if (defined) {
        cert_add("\ndefined");
        for (int i = 0; i < fixed_count; i++) {
            cert_add(" ");
            cert_letter(fixed_name[i]);
            cert_add(" ");
            cert_frac(fixed_value[i]);
        }
    }

    /* Le successioni nominate. Scrivere una definizione può nominarne
     * un'altra: si continua finché ne restano. */
    for (unsigned written = 0, pending; (pending = certificate_sequences & ~written) != 0;) {
        int i = 0;
        while (!(pending >> i & 1)) i++;
        written |= 1u << i;
        if (library[i].definition) {
            cert_add("\ndefine %c m ", library[i].name);
            cert_node(library[i].tree);
            continue;
        }
        cert_add("\nsequence %c %d", library[i].name, library[i].order);
        for (int j = 0; j < library[i].order; j++) cert_add(" %lld", library[i].coef[j]);
        for (int j = 0; j < library[i].order; j++) cert_add(" %lld", library[i].init[j]);
    }
    cert_add("\nend\n");
}

/* Scrive il certificato dell'induzione appena riuscita e lo fa controllare
 * dal verificatore indipendente. statement, base, d, d1 e used sono quelli
 * di induct(): l'enunciato, il caso base, D(n), D(n+1) e l'atomo ricavato
 * dall'ipotesi (o -1).
 *
 * Ritorna la risposta del verificatore, e allora il certificato è in
 * certificate_text; oppure CK_UNSUPPORTED se non si è potuto scrivere. Quando
 * la risposta non è CK_ACCEPTED il motivo è in certificate_problem. */
static CkAnswer certify(const Statement *statement, long long base, Rat d, Rat d1, int used) {
    const char *saved = failure, *why = "", *text;
    Poly a = poly_const(num_int(1)), top = poly_const(num_int(0)), bottom = a;
    CkAnswer answer = CK_UNSUPPORTED;
    int generic = 0;

    /* Il fattore W = top/bottom, con la regola di Ruffini. Le due
     * scomposizioni sono quelle già riuscite in step_holds(): qui possono
     * mancare solo se è finita la memoria. */
    Poly hypothesis[2], part[MAX_DEGREE + 1];
    int degree = used < 0 ? -1 : poly_split(d1.num, used, part, MAX_DEGREE);
    if (used >= 0 && (degree < 0 || poly_split(d.num, used, hypothesis, 1) != 1)) fail(OUT_OF_MEMORY);
    if (used >= 0 && !failure) {
        Poly a_power[MAX_DEGREE + 1], y_power[MAX_DEGREE + 1];
        a = hypothesis[1];

        /* Le potenze di A e di Y = A X. */
        a_power[0] = y_power[0] = poly_const(num_int(1));
        for (int j = 1; j <= degree; j++) {
            a_power[j] = poly_mul(a_power[j - 1], a);
            y_power[j] = poly_mul(y_power[j - 1], poly_mul(a, rat_atom(used).num));
        }

        /* s vale s_j quando entra in Q, poi diventa s_{j-1}. */
        Poly s = part[degree], q = top;
        for (int j = degree - 1; j >= 0; j--) {
            q = poly_add(q, poly_mul(s, y_power[j]), 0);
            s = poly_add(poly_mul(part[j], a_power[degree - j]), poly_mul(hypothesis[0], s), 1);
        }
        top = poly_mul(q, d.den);
        bottom = poly_mul(a_power[degree], d1.den);
    }

    /* Numeratore e denominatore proporzionali: W è un numero. Capita con
     * ogni enunciato "somma = formula", dove W = 1. */
    if (!failure && poly_proportional(top, bottom)) {
        top = poly_const(num_mul(top.term[0].coef, num_inv(bottom.term[0].coef)));
        bottom = poly_const(num_int(1));
    }

    /* L'uguaglianza. Prima senza "generic", poi dichiarando A: dopo un
     * rifiuto si riprova solo se A è un'espressione dei parametri che si può
     * dichiarare diversa da zero. */
    for (; generic < 2 && !failure; generic++) {
        /* 11n. Il verificatore non conosce il teorema del binomio, e una
         * somma con n nel termine non la sa nemmeno leggere come tale: non
         * gli si chiede nulla, e il verdetto dice perché. */
        if (binomial_used) {
            why = "il teorema del binomio non è nella notazione dei certificati";
            break;
        }
        write_certificate(statement, base, top, bottom, generic ? &a : NULL, 0);
        if (certificate_broken) {
            answer = CK_UNSUPPORTED;
            why = "l'enunciato o il passo induttivo usano qualcosa che la notazione dei certificati non ha";
            break;
        }
        text = certificate_text;
        answer = ck_check(&text, &why, checker_steps());
        if (answer != CK_REJECTED || used < 0 || poly_depends_on_n(a)) break;
    }

    /* La definizione. 13c ha stabilito che nel suo punto l'enunciato è
     * definito per ogni n: lo si fa ricontrollare. Se il verificatore non
     * sa decidere resta il certificato della sola uguaglianza; se trova un
     * n in cui l'enunciato non è definito, 13c ha sbagliato. */
    if (answer == CK_ACCEPTED && fixed_count >= 0) {
        const char *doubt = "";
        write_certificate(statement, base, top, bottom, generic ? &a : NULL, 1);
        text = certificate_text;
        CkAnswer full = certificate_broken ? CK_UNSUPPORTED : ck_check(&text, &doubt, checker_steps());
        if (full == CK_REJECTED) {
            answer = CK_REJECTED;
            why = doubt;
        } else if (full == CK_UNSUPPORTED) {
            write_certificate(statement, base, top, bottom, generic ? &a : NULL, 0);
        }
    }

    /* Un errore nei conti del fattore (numeri troppo grandi) non riguarda
     * l'enunciato: vuol dire solo che il certificato non c'è. */
    if (failure) {
        answer = CK_UNSUPPORTED;
        why = failure;
    }
    failure = saved;
    snprintf(certificate_problem, sizeof certificate_problem, "%s%s",
             answer == CK_REJECTED ? "il verificatore indipendente ha respinto il certificato: " : "", why);
    return answer;
}

/* Il motivo con cui induct() rifiuta un enunciato che non è un'uguaglianza.
 * Ha un nome perché prove() (capitolo 20) lo riconosce, e allora passa
 * l'enunciato all'induzione sulle disuguaglianze (capitolo 25). */
const char *const NOT_AN_EQUALITY = "il passo induttivo del capitolo 13 tratta solo le uguaglianze";

/* Il metodo dell'induzione su un enunciato già analizzato: caso base, passo,
 * verifiche e dimostrazione scritta, come descritto in testa al capitolo.
 *
 * variable è la variabile di induzione; se has_base è diverso da zero il caso
 * base è base, altrimenti lo sceglie il programma: il più piccolo n, almeno 1,
 * per cui le somme e i prodotti dell'enunciato hanno almeno un termine.
 * nested dice come scrivere la dimostrazione (vedi put_induction_proof()).
 *
 * Usa la tabella degli atomi così com'è: chi chiama decide se svuotarla. */
static Verdict induct_equality(const Statement *input, int variable, int has_base, long long base, int nested) {
    Verdict verdict = {UNSUPPORTED, variable, base, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    Statement statement = *input;
    induction_var = variable;
    default_base = 1;
    domain_floor = has_base ? base : 1;
    if (statement.relation != REL_EQ) { verdict.reason = NOT_AN_EQUALITY; return verdict; }

    /* D(n). È la prima valutazione, quindi quella che fa nascere gli atomi con
     * gli estremi scritti nell'enunciato, e che calcola default_base. */
    Rat n = rat_atom(atom_var(variable));
    Rat d = difference(&statement, n);
    if (failure) { verdict.reason = failure; return verdict; }
    if (!has_base) base = default_base;
    verdict.base = base;

    /* 13a. Caso base. */
    Rat d0 = difference(&statement, rat_int(base));
    int base_holds = !failure && poly_vanishes(d0.num);
    if (failure) { verdict.reason = failure; return verdict; }
    if (!base_holds) {
        /* Un numero diverso da zero è una smentita certa. Un'espressione con
         * dei parametri potrebbe invece essere uno zero che l'algebra non sa
         * riconoscere: non si può concludere nulla. */
        Num value;
        if (rat_number(d0, &value)) { verdict.outcome = REFUTED; verdict.witness = base; }
        else { verdict.outcome = NOT_PROVED; verdict.reason = "il caso base non si riduce a zero"; }
        return verdict;
    }

    /* 13b. Passo induttivo. */
    Rat d1 = difference(&statement, rat_add(n, rat_int(1), 0));
    if (failure) { verdict.reason = failure; return verdict; }
    int used;
    int proved = step_holds(d, d1, &used);
    if (failure) { verdict.reason = failure; return verdict; }
    if (proved) {
        /* 13c, 13d, 13e. Verifica indipendente, con i numeri al posto delle lettere. */
        const char *problem = verify_instances(&statement, base, 1);
        if (problem) {
            verdict.outcome = NOT_PROVED;
            verdict.reason = problem;
            return verdict;
        }

        /* 13f, 13g. La dimostrazione scritta, con i suoi passaggi. */
        put_induction_proof(&statement, base, d, used, nested);

        /* 13h. Il certificato. Un rifiuto vuol dire che il motore e il
         * verificatore non sono d'accordo: nel dubbio non è dimostrato, e
         * l'enunciato va guardato come un errore del programma. */
        CkAnswer answer = certify(&statement, base, d, d1, used);
        if (answer == CK_REJECTED) {
            unjustified_steps++;
            verdict.outcome = NOT_PROVED;
            verdict.reason = certificate_problem;
            return verdict;
        }
        if (answer == CK_ACCEPTED) verdict.certificate = certificate_text;
        else verdict.reason = certificate_problem;
        verdict.outcome = PROVED;
        verdict.proof = proof_text;
        return verdict;
    }

    /* Ricerca di un controesempio nei valori successivi al caso base. Un
     * errore qui (per esempio numeri troppo grandi) interrompe solo la
     * ricerca. */
    for (long long c = base + 1; c <= base + SEARCH_SPAN; c++) {
        Num value;
        Rat dc = difference(&statement, rat_int(c));
        if (failure) break;
        if (rat_number(dc, &value) && !num_is_zero(value)) {
            verdict.outcome = REFUTED;
            verdict.witness = c;
            return verdict;
        }
    }
    failure = NULL;
    verdict.outcome = NOT_PROVED;
    verdict.reason = "il passo induttivo non si chiude";
    return verdict;
}

/* Dimostra per induzione l'enunciato input: è induct_equality(), con il
 * teorema del binomio (11n) tra le regole di calcolo. La regola è permessa
 * solo qui perché è qui che la dimostrazione scritta la dichiara
 * (put_induction_proof()) e che il certificato dice di non saperla
 * esprimere (certify()): altrove verrebbe usata in silenzio. */
Verdict induct(const Statement *input, int variable, int has_base, long long base, int nested) {
    binomial_ok = 1;
    binomial_used = 0;
    Verdict verdict = induct_equality(input, variable, has_base, base, nested);
    binomial_ok = 0;
    return verdict;
}

/* Prova a dimostrare per induzione l'enunciato scritto in formula, con la
 * variabile di induzione e il caso base indicati (vedi induct()).
 *
 * Svuota l'arena e la tabella degli atomi: i risultati di chiamate precedenti
 * non sono più validi. */
Verdict prove_by_induction(const char *formula, int variable, int has_base, long long base) {
    Verdict verdict = {UNSUPPORTED, variable, base, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    Statement statement;

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
    return induct(&statement, variable, has_base, base, 0);
}
