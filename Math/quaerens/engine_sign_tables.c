/* MODULO engine_sign_tables: la tabella dei segni: punti esatti, segni, righe,
 * soluzioni, grafici, un parametro (capitoli 18.8-18.19).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_sign_tables.h,
 * e il resto è static. */
#include "engine_sign_tables.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"
#include "engine_intervals.h"
#include "engine_quantifiers.h"

/* =============================================================================
 * 18.8 LA TABELLA DEI SEGNI (18p): NUMERI E POLINOMI ESATTI, I PUNTI
 * ============================================================================
 *
 * Questo capitolo e i seguenti, fino al 18.16, sono la regola 18p. Qui il
 * metodo e la sua parte esatta: i razionali a 128 bit, i polinomi in una
 * variabile, le catene di Sturm, la base e i punti della tabella. Le lettere
 * per esponenziali, logaritmi e funzioni goniometriche sono nel capitolo 18.9,
 * l'albero dei segni nel 18.10, i confronti preparati nel 18.11, i controlli
 * con i numeri nel 18.12, le righe e le soluzioni nei 18.13 e 18.14, il
 * grafico nel 18.15, il verdetto e il certificato nel 18.16.
 *
 * 18p. UNA SOLA VARIABILE: LA TABELLA DEI SEGNI
 *
 * Gli enunciati di questa regola hanno una variabile sola, che varia nei
 * numeri reali o nei razionali, e confrontano espressioni razionali con =,
 * \neq, <, \le, >, \ge. Sono le equazioni e le disequazioni dei libri di
 * scuola scritte insieme al loro risultato, per esempio
 *
 *     \forall x \in \mathbb{R}\ (\frac{x - 2}{x + 3} \ge 0 \iff (x < -3 \lor x \ge 2))
 *
 * Che cosa vuol dire un confronto dove un'espressione non è definita. In
 * x = -3 la frazione non ha valore. La convenzione è quella dei libri: un
 * confronto vale in x solo se le espressioni che contiene sono definite in
 * x, quindi -3 non è una soluzione della disequazione. È una convenzione
 * diversa da quella del resto del capitolo, dove un'espressione non definita
 * ferma la dimostrazione: qui "per ogni x, A(x) se e solo se B(x)" confronta
 * due insiemi di soluzioni, e la dimostrazione scritta lo ricorda.
 *
 * Il metodo decide ogni enunciato di questa forma: risponde vero o falso,
 * mai "non so", salvo che i numeri escano dall'aritmetica esatta.
 *
 *   18p-1. Ogni confronto si porta alla forma N(x)/D(x) ? 0, con N e D
 *          polinomi a coefficienti interi. Che sia vero in x dipende solo
 *          dal segno di N e di D in x, e dal fatto che i divisori incontrati
 *          nel conto, anch'essi polinomi, lì siano diversi da zero.
 *
 *   18p-2. Un polinomio cambia segno solo passando per una sua radice: è
 *          una funzione continua, e per il teorema degli zeri tra un valore
 *          positivo e uno negativo ne assume uno nullo. Tra due radici
 *          consecutive di tutti i polinomi in gioco ogni segno è dunque
 *          costante, e con i segni lo è la verità dell'enunciato. Basta
 *          guardarla in ogni radice e in un punto qualsiasi di ogni
 *          intervallo tra due radici: è la tabella dei segni.
 *
 *   18p-3. Le radici non serve calcolarle, basta separarle. Teorema di
 *          Sturm: per un polinomio p senza radici multiple si costruisce la
 *          catena p_0 = p, p_1 = p', p_{i+1} = -resto(p_{i-1} : p_i), fino a
 *          una costante. Detto V(x) il numero di cambi di segno nella lista
 *          p_0(x), p_1(x), ... (saltando gli zeri), il numero di radici
 *          reali di p tra a e b, con a < b che non sono radici, è
 *          V(a) - V(b). Dimezzando un intervallo che le contiene tutte si
 *          arriva a intervalli con una radice sola ciascuno.
 *
 *   18p-4. Polinomi diversi possono avere radici in comune, e allora due
 *          intervalli potrebbero nascondere la stessa radice. Lo si evita
 *          lavorando su una "base": polinomi senza radici multiple e a due a
 *          due senza radici comuni, di cui ogni polinomio in gioco è un
 *          prodotto (a meno di esponenti). La si costruisce con il massimo
 *          comun divisore: se g = mcd(a, b) non è costante, al posto di a e
 *          b si mettono a/g, b/g e g. Radici di elementi diversi della base
 *          sono numeri diversi, quindi stringendo gli intervalli prima o poi
 *          si separano.
 *
 *   18p-5. Il segno di un polinomio p in una radice r, isolata in (a, b), di
 *          un elemento q della base. Se q divide p, p(r) = 0. Altrimenti p e
 *          q non hanno radici comuni, p non si annulla in tutto (a, b)
 *          (l'unica radice lì dentro è r) e ha quindi il segno che ha nel
 *          punto medio, che è un numero razionale e si calcola.
 *
 *   18p-6. Un elemento della base di grado quattro o più si prova a
 *          scomporlo in fattori di secondo grado (uni_quadratic_factor()).
 *          Alla decisione non serve: serve a scrivere le radici con i
 *          radicali, come sui libri, invece che con un nome.
 *
 * Le regole che seguono portano alla stessa tabella confronti che non sono
 * tra frazioni di polinomi; ognuna è spiegata dove è scritta.
 *
 *   18p-7.  Radici quadrate e valori assoluti: ogni radice è una lettera, e
 *           il segno di P + Q s viene da quelli di P, Q e P^2 - Q^2 R.
 *   18p-8.  Esponenziali e logaritmi: una lettera per p^(x/L) o per
 *           log_b f(x), con i suoi gradini.
 *   18p-9.  Monomi di potenze di basi diverse.
 *   18p-10. Numeri con logaritmi, e e pi tra i coefficienti e gli estremi.
 *   18p-11. Funzioni goniometriche: la lettera t = tan(u / 2).
 *   18p-12. Le soluzioni di una condizione periodica, scritte con k.
 *   18p-13. Le famiglie x = a + k T di un risultato, dentro un enunciato.
 *   18p-14. Le finestre: una condizione periodica ristretta a un intervallo.
 *
 * E una regola che non decide nulla, ma fa ricontrollare ciò che si è
 * deciso:
 *
 *   18p-15. Il certificato: la tabella, data a checker.c, che la ricontrolla
 *           per conto suo (capitolo 12 di checker.c).
 *
 * Le radici razionali si trovano a parte, con il teorema delle radici
 * razionali, e si tolgono: così ogni punto medio, che è razionale, non è mai
 * una radice, e nei numeri razionali si sa quali punti della tabella contano.
 *
 * Risolvere. La stessa tabella dà l'insieme delle soluzioni di una
 * condizione, \{x \in \mathbb{R} \mid ...\}: le righe consecutive in cui la
 * condizione vale sono un intervallo o un punto, e messe in fila sono la
 * risposta (sign_solution()). Nessuna formula risolutiva per un tipo di
 * equazione: è lo stesso metodo generale, letto in un altro modo.
 *
 * I controlli indipendenti sono due, e nessuno dei due usa polinomi in una
 * variabile o radici. Il primo rifà ogni riga della tabella. Una riga con un
 * valore razionale si rifà sostituendo il numero nell'enunciato, con il
 * calcolo esatto (sign_holds_at()); una riga in una radice irrazionale, in
 * un punto come ln 3, o di un enunciato periodico si rifà con gli intervalli
 * del capitolo 24 (range_truth()), dove un segno è certo oppure non si sa, e
 * un'uguaglianza si può solo trovare compatibile. Ogni intervallo si prova
 * anche in altri punti oltre a quello scelto (row_points()). Una riga
 * smentita è un errore del programma; una riga razionale che non si riesce a
 * rifare lascia l'enunciato non deciso. Il secondo rilegge le soluzioni
 * scritte, con il lettore del programma, e le confronta con la tabella
 * (solution_reread()); per una condizione periodica le confronta con la
 * condizione, calcolata con gli intervalli in molti valori e negli estremi
 * scritti. Ciò che resta scoperto: la rilettura quando una radice non ha
 * una scrittura con i radicali e riceve un nome; il verdetto lo dichiara.
 * Lì il controllo è quello degli script di tools/fuzz/, i cui oracoli fanno
 * i conti per conto loro.
 *
 * Il terzo controllo, dove arriva, è il certificato (18p-15): con frazioni
 * di polinomi e valori assoluti, senza radici, esponenziali, logaritmi e
 * funzioni goniometriche, la tabella intera va al verificatore, che ne
 * ricava da capo i polinomi, ne riconta le radici con le catene di Sturm e
 * ricalcola la verità di ogni riga. DIMOSTRATO, FALSO e RISOLTO valgono
 * allora solo se il verificatore accetta.
 */

/* Il messaggio quando un conto della tabella esce dai 128 bit. */
const char *const SIGN_LIMIT = "numeri troppo grandi per la tabella dei segni";

/* Ritorna num/den ridotta, con den diverso da zero. */
static Wide wide_make(__int128 num, __int128 den) {
    __int128 g = gcd128(num, den);
    if (den < 0) g = -g;
    return (Wide){num / g, den / g};
}

/* Ritorna il segno di a - b. */
static int wide_cmp(Wide a, Wide b) {
    __int128 left, right;
    if (__builtin_mul_overflow(a.num, b.den, &left) || __builtin_mul_overflow(b.num, a.den, &right)) { fail(SIGN_LIMIT); return 0; }
    return (left > right) - (left < right);
}

/* Ritorna il punto medio tra a e b. */
static Wide wide_mid(Wide a, Wide b) {
    __int128 x, y, den;
    if (__builtin_mul_overflow(a.num, b.den, &x) || __builtin_mul_overflow(b.num, a.den, &y) || __builtin_add_overflow(x, y, &x) ||
        __builtin_mul_overflow(a.den, b.den, &den) || __builtin_mul_overflow(den, (__int128)2, &den)) { fail(SIGN_LIMIT); return a; }
    return wide_make(x, den);
}

/* Ritorna a + b. */
static Wide wide_add(Wide a, Wide b) {
    __int128 x, y, den;
    if (__builtin_mul_overflow(a.num, b.den, &x) || __builtin_mul_overflow(b.num, a.den, &y) || __builtin_add_overflow(x, y, &x) ||
        __builtin_mul_overflow(a.den, b.den, &den)) { fail(SIGN_LIMIT); return a; }
    return wide_make(x, den);
}

/* Ritorna a * b. */
static Wide wide_mul(Wide a, Wide b) {
    __int128 num, den;
    if (__builtin_mul_overflow(a.num, b.num, &num) || __builtin_mul_overflow(a.den, b.den, &den)) { fail(SIGN_LIMIT); return a; }
    return wide_make(num, den);
}

/* Ritorna la parte intera della radice quadrata di v, con 0 <= v < 2^126.
 * Metodo di Newton sugli interi: partendo da una stima per eccesso, la
 * successione r -> (r + v / r) / 2 scende, e si ferma sulla parte intera
 * della radice. */
static __int128 wide_isqrt(__int128 v) {
    if (v < 2) return v;
    __int128 r = (__int128)1 << 63;
    for (;;) {
        __int128 next = (r + v / r) / 2;
        if (next >= r) return r;
        r = next;
    }
}

/* Ritorna un razionale strettamente tra a e b, con a < b: quello con il
 * denominatore più piccolo, se ne esiste uno con denominatore fino a 64,
 * altrimenti il punto medio.
 *
 * Perché non sempre il punto medio: è il valore in cui si calcola una riga
 * della tabella, e il controllo indipendente lo sostituisce nell'enunciato
 * con le frazioni a 64 bit. Un'espressione di grado 9 in -31/16 ne esce, in
 * -7/4 no; e nella dimostrazione scritta "per esempio x = -7/4" si legge
 * meglio. */
static Wide wide_between(Wide a, Wide b) {
    for (__int128 d = 1; d <= 64 && !failure; d++) {
        /* Il più piccolo n con n/d > a è la parte intera di a d, più uno. La
         * divisione del C tronca verso lo zero: per i negativi si corregge. */
        __int128 scaled, n;
        if (__builtin_mul_overflow(a.num, d, &scaled)) break;
        n = scaled / a.den - (scaled % a.den < 0) + 1;

        /* n/d è ridotta: se non lo fosse, un denominatore più piccolo avrebbe
         * già dato lo stesso numero. */
        if (wide_cmp((Wide){n, d}, b) < 0) return (Wide){n, d};
    }
    return wide_mid(a, b);
}

/* Ristabilisce l'invariante dopo un conto che può aver annullato i
 * coefficienti più alti. */
static void uni_trim(Uni *p) {
    while (p->degree >= 0 && p->c[p->degree] == 0) p->degree--;
}

/* Divide p per il massimo comun divisore dei suoi coefficienti, che è
 * positivo: non cambia né le radici né i segni, e tiene piccoli i numeri. */
static void uni_primitive(Uni *p) {
    __int128 g = 0;
    for (int i = 0; i <= p->degree; i++) g = gcd128(g, p->c[i]);
    for (int i = 0; g > 1 && i <= p->degree; i++) p->c[i] /= g;
}

/* Cambia segno a p. */
static void uni_negate(Uni *p) {
    for (int i = 0; i <= p->degree; i++) p->c[i] = -p->c[i];
}

/* Ritorna 1 se a e b sono lo stesso polinomio. */
static int uni_equal(const Uni *a, const Uni *b) {
    return a->degree == b->degree && memcmp(a->c, b->c, sizeof a->c[0] * (size_t)(a->degree + 1)) == 0;
}

/* Ritorna la derivata di p. */
static Uni uni_derivative(const Uni *p) {
    Uni d;
    d.degree = p->degree > 0 ? p->degree - 1 : -1;
    for (int i = 1; i <= p->degree; i++)
        if (__builtin_mul_overflow(p->c[i], (__int128)i, &d.c[i - 1])) fail(SIGN_LIMIT);
    return d;
}

/* Ritorna un multiplo positivo del resto della divisione di a per b, che non
 * è il polinomio nullo.
 *
 * Per restare tra gli interi a ogni passo si moltiplica il resto per il
 * coefficiente direttivo di b prima di togliergli il multiplo di b che ne
 * annulla il termine più alto. Se quel coefficiente è negativo il segno si
 * rovescia: `negative` tiene il conto, perché alla catena di Sturm serve il
 * resto vero a meno di un fattore positivo, non a meno del segno. */
static Uni uni_remainder(const Uni *a, const Uni *b) {
    Uni r = *a;
    int negative = 0;
    while (r.degree >= b->degree && !failure) {
        __int128 lead = r.c[r.degree], scale = b->c[b->degree], part;
        int shift = r.degree - b->degree;
        for (int i = 0; i <= r.degree; i++) {
            if (__builtin_mul_overflow(r.c[i], scale, &r.c[i])) fail(SIGN_LIMIT);
            if (i >= shift && (__builtin_mul_overflow(lead, b->c[i - shift], &part) || __builtin_sub_overflow(r.c[i], part, &r.c[i]))) fail(SIGN_LIMIT);
        }
        if (scale < 0) negative = !negative;
        uni_trim(&r);
        uni_primitive(&r);
    }
    if (negative) uni_negate(&r);
    return r;
}

/* Ritorna il massimo comun divisore di a e b, con coefficienti senza
 * divisori comuni e coefficiente direttivo positivo (algoritmo di Euclide:
 * mcd(a, b) = mcd(b, resto)). */
static Uni uni_gcd(Uni a, Uni b) {
    while (b.degree >= 0 && !failure) {
        Uni r = uni_remainder(&a, &b);
        a = b;
        b = r;
    }
    uni_primitive(&a);
    if (a.degree >= 0 && a.c[a.degree] < 0) uni_negate(&a);
    return a;
}

/* Se b divide a mette il quoziente in *q e ritorna 1, altrimenti ritorna 0.
 * b non è nullo e i suoi coefficienti non hanno divisori comuni: allora, per
 * il lemma di Gauss, se divide a il quoziente ha coefficienti interi, e la
 * divisione si fa tra interi. */
int uni_divide(const Uni *a, const Uni *b, Uni *q) {
    Uni r = *a;
    q->degree = a->degree - b->degree;
    if (a->degree < 0) { q->degree = -1; return 1; }
    if (q->degree < 0) return 0;
    for (int i = q->degree; i >= 0; i--) {
        __int128 lead = r.c[i + b->degree], part;
        if (lead % b->c[b->degree] != 0) return 0;
        q->c[i] = lead / b->c[b->degree];
        for (int j = 0; j <= b->degree; j++)
            if (__builtin_mul_overflow(q->c[i], b->c[j], &part) || __builtin_sub_overflow(r.c[i + j], part, &r.c[i + j])) { fail(SIGN_LIMIT); return 0; }
    }
    for (int i = 0; i < b->degree; i++)
        if (r.c[i] != 0) return 0;
    return 1;
}

/* Ritorna il segno di p nel razionale x. Schema di Horner senza frazioni:
 * con x = n/d si calcola il segno di p(x) d^degree, che è lo stesso perché
 * d è positivo.
 *
 * Per un polinomio di grado alto quel numero può non stare in 128 bit: capita
 * con gli angoli multipli della goniometria, dove sin(7u) è una frazione di
 * grado 14 in t. Allora il segno si prende con gli intervalli del capitolo
 * 24: lo stesso schema di Horner, in cui ogni operazione allarga l'intervallo
 * quanto basta a contenere il risultato vero. Se l'intervallo finale non
 * contiene lo zero il segno è certo. Se lo contiene, p(x) è zero oppure è
 * solo troppo vicino a zero per questi numeri: è zero esattamente quando
 * d t - n divide p, e la divisione è un conto tra interi; altrimenti non si
 * risponde. */
int uni_sign_at(const Uni *p, Wide x) {
    __int128 value = 0, power = 1, term;
    int exact = 1, side = 0;
    for (int i = p->degree; i >= 0 && exact; i--)
        exact = !(__builtin_mul_overflow(value, x.num, &value) || __builtin_mul_overflow(p->c[i], power, &term) ||
                  __builtin_add_overflow(value, term, &value) || (i > 0 && __builtin_mul_overflow(power, x.den, &power)));
    if (exact) return (value > 0) - (value < 0);
    Range at = range_ratio(x.num, x.den), sum = {0, 0};
    Uni linear = {1, {-x.num, x.den}}, quotient;
    for (int i = p->degree; i >= 0; i--) sum = range_add(range_mul(sum, at), range_ratio(p->c[i], 1));
    if (range_side(sum, &side)) return side;
    if (!failure && !uni_divide(p, &linear, &quotient)) fail(SIGN_LIMIT);
    return 0;
}

/* Legge il polinomio negli atomi p come polinomio nel solo atomo x a
 * coefficienti razionali, moltiplicato per x^*shift se x vi compare con
 * esponenti negativi (un denominatore fatto di sole x): mette in *out il
 * polinomio a coefficienti interi che ha gli stessi segni di p x^*shift.
 * Ritorna 0 se p non ha questa forma: un altro atomo, un esponente non
 * intero, un coefficiente complesso, un grado oltre MAX_UNI. */
int uni_from_poly(Poly p, int x, Uni *out, int *shift) {
    __int128 scale = 1;
    long long low = 0;
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        Frac e = t->mono.count ? t->mono.factor[0].exp : frac_int(0);
        if (t->mono.count > 1 || (t->mono.count == 1 && t->mono.factor[0].atom != x) || e.den != 1 || t->coef.im.num != 0) return 0;
        if (e.num < low) low = e.num;
        scale = scale / gcd128(scale, t->coef.re.den) * t->coef.re.den;
        if (scale > COEF_LIMIT) { fail(SIGN_LIMIT); return 0; }
    }
    *shift = (int)-low;
    out->degree = -1;
    memset(out->c, 0, sizeof out->c);
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        long long e = (t->mono.count ? t->mono.factor[0].exp.num : 0) - low;
        if (e > MAX_UNI) return 0;
        out->c[e] = (__int128)t->coef.re.num * (scale / t->coef.re.den);
        if (e > out->degree) out->degree = (int)e;
    }
    return 1;
}

/* La catena di Sturm del polinomio di cui si stanno separando le radici
 * (18p-3): sturm_length polinomi, il primo è il polinomio stesso. */
static Uni sturm[MAX_UNI + 2];
static int sturm_length;

/* Costruisce la catena di Sturm di p, che non ha radici multiple. */
static void sturm_build(const Uni *p) {
    sturm[0] = *p;
    sturm[1] = uni_derivative(p);
    sturm_length = 2;
    while (sturm[sturm_length - 1].degree > 0 && !failure) {
        Uni r = uni_remainder(&sturm[sturm_length - 2], &sturm[sturm_length - 1]);
        if (r.degree < 0) break;
        uni_negate(&r);
        sturm[sturm_length++] = r;
    }
}

/* Ritorna V(x): quanti cambi di segno ha la catena di Sturm nel razionale x,
 * saltando gli zeri. */
static int sturm_changes(Wide x) {
    int changes = 0, last = 0;
    for (int i = 0; i < sturm_length; i++) {
        int sign = uni_sign_at(&sturm[i], x);
        if (sign && last && sign != last) changes++;
        if (sign) last = sign;
    }
    return changes;
}

/* I polinomi dell'enunciato in corso: numeratori, denominatori e divisori
 * dei suoi confronti. La tabella dei segni ha una colonna per ognuno. */
static Uni sign_poly[MAX_CRITICAL];
static int sign_polys;

/* La base di 18p-4: polinomi senza radici multiple, a due a due senza radici
 * comuni, coefficienti senza divisori comuni e coefficiente direttivo
 * positivo. Ogni radice di un polinomio di sign_poly[] è radice di uno e un
 * solo elemento. Dopo sign_points() gli elementi di grado almeno 2 non hanno
 * più radici razionali. */
Uni sign_base[2 * MAX_CRITICAL];
int sign_bases;

/* Aggiunge al testo text, di size byte, un pezzo con la sintassi di printf.
 * Se non ci sta annota un errore: un testo troncato non si può presentare
 * come risultato. */
void text_add(char *text, size_t size, const char *format, ...) {
    size_t used = strlen(text);
    va_list args;
    va_start(args, format);
    int wanted = vsnprintf(text + used, size - used, format, args);
    va_end(args);
    if (wanted < 0 || (size_t)wanted >= size - used) fail("risultato troppo lungo da scrivere");
}

/* Aggiunge a text, di size byte, il razionale v in LaTeX: 3, -\frac{5}{2}. */
static void wide_latex(Wide v, char *text, size_t size) {
    if (v.den == 1) text_add(text, size, "%lld", (long long)v.num);
    else text_add(text, size, "%s\\frac{%lld}{%lld}", v.num < 0 ? "-" : "", (long long)(v.num < 0 ? -v.num : v.num), (long long)v.den);
}

/* Scrive nella dimostrazione il razionale v, in LaTeX come wide_latex(): due
 * numeri di 64 bit e la frazione stanno comodamente in text. */
void put_wide(Wide v) {
    char text[96] = "";
    wide_latex(v, text, sizeof text);
    proof_add("%s", text);
}

/* Scrive in text, di size byte, il razionale v come testo semplice: 3, -5/2. */
static void wide_text(Wide v, char *text, size_t size) {
    if (v.den == 1) snprintf(text, size, "%lld", (long long)v.num);
    else snprintf(text, size, "%lld/%lld", (long long)v.num, (long long)v.den);
}

/* Aggiunge a text, di size byte, il polinomio p nella lettera name, in LaTeX. */
void uni_latex(const Uni *p, int name, char *text, size_t size) {
    if (p->degree < 0) text_add(text, size, "0");
    for (int i = p->degree, first = 1; i >= 0; i--) {
        __int128 c = p->c[i], magnitude = c < 0 ? -c : c;
        if (c == 0) continue;
        text_add(text, size, "%s", first ? (c < 0 ? "-" : "") : (c < 0 ? " - " : " + "));
        if (magnitude != 1 || i == 0) text_add(text, size, "%lld", (long long)magnitude);
        if (i > 0) text_add(text, size, "%c", name);
        if (i > 1) text_add(text, size, "^{%d}", i);
        first = 0;
    }
}

/* Scrive nella dimostrazione il polinomio p nella lettera name. */
void put_uni(const Uni *p, int name) {
    char text[512] = "";
    uni_latex(p, name, text, sizeof text);
    proof_add("%s", text);
}

/* Porta fuori dalla radice quadrata di *inside i suoi fattori quadrati, come
 * in sqrt(12) = 2 sqrt(3): lascia in *inside ciò che resta sotto la radice e
 * ritorna il numero che va davanti, così che il radicando di partenza sia
 * quel numero al quadrato per *inside. Si provano i fattori fino a 100000:
 * un quadrato più grande resta dentro, e la scrittura è giusta, solo meno
 * semplice. */
static __int128 square_out(__int128 *inside) {
    __int128 outside = 1;
    for (__int128 f = 2; f * f <= *inside && f < 100000; f++)
        while (*inside % (f * f) == 0) { *inside /= f * f; outside *= f; }
    return outside;
}

/* Aggiunge a text, di size byte, una radice del polinomio di secondo grado
 * q = a x^2 + b x + c, che ha due radici reali irrazionali, scritta con i
 * radicali; smaller dice se è la più piccola delle due. Ritorna 0, senza
 * scrivere nulla, se q non ha grado due o ha coefficienti troppo grandi.
 *
 * Le radici sono (-b - sqrt(D)) / 2a e (-b + sqrt(D)) / 2a con
 * D = b^2 - 4ac, e quella con il segno meno, portato il denominatore a
 * essere positivo, è la più piccola. Da sqrt(D) si portano fuori i
 * quadrati: sqrt(12) = 2 sqrt(3). */
int quadratic_latex(const Uni *q, int smaller, char *text, size_t size) {
    __int128 limit = (__int128)1 << 30, a = q->c[2], b = q->c[1], c = q->c[0];
    if (q->degree != 2 || a >= limit || a <= -limit || b >= limit || b <= -limit || c >= limit || c <= -limit) return 0;

    /* (top + side * outside * sqrt(inside)) / bottom, con bottom > 0. */
    __int128 inside = b * b - 4 * a * c, top = a < 0 ? b : -b, bottom = a < 0 ? -2 * a : 2 * a;
    __int128 outside = square_out(&inside);
    __int128 g = gcd128(gcd128(top, outside), bottom);
    top /= g; outside /= g; bottom /= g;
    if (bottom != 1 && top == 0 && smaller) text_add(text, size, "-");
    if (bottom != 1) text_add(text, size, "\\frac{");
    if (top != 0) text_add(text, size, "%lld %s ", (long long)top, smaller ? "-" : "+");
    else if (smaller && bottom == 1) text_add(text, size, "-");
    if (outside != 1) text_add(text, size, "%lld", (long long)outside);
    text_add(text, size, "\\sqrt{%lld}", (long long)inside);
    if (bottom != 1) text_add(text, size, "}{%lld}", (long long)bottom);
    return 1;
}

/* Un numero reale che non è radice di un polinomio a coefficienti razionali,
 * e che entra nella tabella come punto: log_2 3, e^2. Lo si conosce con un
 * intervallo che lo contiene (capitolo 24) e con il testo che lo scrive. */
typedef struct {
    Range value;
    char text[96];  /* in LaTeX, come va scritto nelle soluzioni */
    int exact;      /* 1 se number è valido */
    Rat number;     /* lo stesso numero come frazione negli atomi che sono
                       numeri (logaritmi di primi, il numero e): serve a
                       riconoscere due scritture dello stesso numero */
} Kappa;

/* I numeri così dell'enunciato in corso: li aggiunge sign_column_kappa(). */
static Kappa kappa[MAX_KAPPAS];
int kappas;

/* I due tipi di spazio (18p-8). */
typedef enum {
    SPACE_EXP,  /* la lettera è p^(x/L): un esponenziale, sempre positivo */
    SPACE_LOG   /* la lettera è il logaritmo in base b di un'espressione */
} SpaceKind;

/* Un gradino di uno spazio: una radice reale di un polinomio nella lettera
 * dello spazio, cioè un valore in cui un confronto può cambiare. Il valore è
 * il razionale low (exact = 1) oppure la sola radice di element tra low e
 * high. Dire che la lettera sta sopra, sotto o sul gradino è un confronto
 * nella variabile dell'enunciato: lo dà above (il segno di left - right),
 * oppure la colonna kappa quando il confronto è con un numero che non è
 * radice di un polinomio. */
typedef struct {
    int exact;             /* 1 se il gradino è il razionale low */
    Wide low, high;        /* l'intervallo chiuso che lo contiene */
    Uni element;           /* gradino irrazionale: il polinomio di cui è la sola
                              radice tra low e high */
    const Formula *above;  /* NULL se si usa kappa */
    int kappa;             /* posto in sign_poly[], o -1 */
} Step;

/* Uno spazio: una funzione della variabile, crescente, che nei conti della
 * tabella è una lettera sola. I polinomi nella lettera sono colonne con il
 * numero dello spazio in sign_space[]; i gradini, in ordine crescente, sono
 * le loro radici reali. Gli spazi valgono per l'enunciato in corso. */
typedef struct {
    SpaceKind kind;
    long long prime;       /* SPACE_EXP: il primo p; 0 per il numero e */
    long long scale;       /* SPACE_EXP: L, con la lettera uguale a p^(x/L) */
    Frac base;             /* SPACE_LOG: la base b > 1 */
    int natural;           /* SPACE_LOG: 1 se la base è il numero e */
    const Node *argument;  /* SPACE_LOG: l'argomento, com'è scritto */
    int letter;            /* l'atomo che sta per la funzione */
    int steps;             /* quanti gradini, in step[] */
    Step step[MAX_STEPS];  /* i gradini, in ordine crescente (space_process()) */
} Space;

/* Gli spazi dell'enunciato in corso: li crea space_collect(), con
 * space_exp() e space_log(). */
static Space space[MAX_SPACES];
int spaces;

/* Lo stato della tabella che serve agli agganci di eval(): space_live è 1
 * mentre si prepara un confronto (solo allora potenze e logaritmi diventano
 * lettere); space_seen ha il bit s se nel confronto in corso è comparso il
 * logaritmo dello spazio s; sign_name e sign_x sono la variabile
 * dell'enunciato, come lettera e come atomo. */
static int space_live;
static unsigned space_seen;
static int sign_name, sign_x;

/* I punti dell'enunciato in corso. Dopo sign_points() sono in ordine
 * crescente e i loro intervalli chiusi [low, high] non si toccano. */
Critical sign_point[MAX_POINTS];
int sign_points_count;

/* Che cos'è ogni colonna, oltre al suo polinomio. sign_space[i] dice in
 * quale lettera è il polinomio: -1 nella variabile dell'enunciato,
 * altrimenti nella lettera dello spazio con quel numero (18p-8).
 * sign_kappa[i], se non è -1, dice che la colonna non ha un polinomio: è il
 * segno di x - kappa[sign_kappa[i]], che si legge dalla posizione della riga
 * rispetto a quel punto. */
static int sign_space[MAX_CRITICAL], sign_kappa[MAX_CRITICAL];

/* Ritorna il posto in sign_poly[] del polinomio p nella lettera dello spazio
 * `where` (-1: la variabile), aggiungendolo se manca. Lo si conserva senza
 * divisori comuni tra i coefficienti; il segno resta. */
static int sign_column_in(Uni p, int where) {
    uni_primitive(&p);
    for (int i = 0; i < sign_polys; i++)
        if (sign_space[i] == where && sign_kappa[i] < 0 && uni_equal(&sign_poly[i], &p)) return i;
    if (sign_polys == MAX_CRITICAL) { fail("troppi polinomi diversi nella tabella dei segni"); return 0; }
    sign_poly[sign_polys] = p;
    sign_space[sign_polys] = where;
    sign_kappa[sign_polys] = -1;
    return sign_polys++;
}

/* Lo stesso, per un polinomio nella variabile dell'enunciato. */
static int sign_column(Uni p) { return sign_column_in(p, -1); }

/* Ritorna il posto della colonna "x - k", dove k è il numero che sta
 * nell'intervallo value e si scrive text; la aggiunge se manca. number, se
 * non è NULL, è lo stesso numero come frazione esatta. Due numeri sono lo
 * stesso se sono scritti allo stesso modo, o se la differenza delle loro
 * frazioni esatte è la frazione nulla: così log_3 2 e ln 2 / ln 3, che
 * nascono da due parti diverse di un enunciato, sono un punto solo. Senza
 * questo sarebbero due punti impossibili da separare. */
static int sign_column_kappa(Range value, const char *text, const Rat *number) {
    for (int i = 0; i < sign_polys; i++) {
        if (sign_kappa[i] < 0) continue;
        const Kappa *other = &kappa[sign_kappa[i]];
        if (strcmp(other->text, text) == 0 || (number && other->exact && rat_add(*number, other->number, 1).num.count == 0)) return i;
    }
    if (sign_polys == MAX_CRITICAL || kappas == MAX_KAPPAS || strlen(text) >= sizeof kappa[0].text || !range_known(value)) {
        fail("troppi punti con logaritmi nella tabella dei segni, o un punto che non so calcolare");
        return 0;
    }
    kappa[kappas].value = value;
    kappa[kappas].exact = number != NULL;
    if (number) kappa[kappas].number = *number;
    strcpy(kappa[kappas].text, text);
    sign_poly[sign_polys] = (Uni){-1, {0}};
    sign_space[sign_polys] = -1;
    sign_kappa[sign_polys] = kappas++;
    return sign_polys++;
}

/* Aggiunge un elemento alla base, se c'è posto. */
static void base_append(Uni p) {
    if (sign_bases == 2 * MAX_CRITICAL) { fail("troppi polinomi diversi nella tabella dei segni"); return; }
    sign_base[sign_bases++] = p;
}

/* 18p-4. Inserisce nella base le radici di p, che non è costante.
 *
 * Prima si tolgono a p le radici multiple: s = p / mcd(p, p') ha le stesse
 * radici, ognuna una volta sola. Poi s si confronta con ogni elemento b: se
 * hanno un fattore comune g, b diventa b/g, g entra nella base come elemento
 * nuovo e s diventa s/g. I pezzi restano senza radici comuni perché né b né
 * s hanno radici multiple. Ciò che avanza di s è un elemento nuovo. */
static void base_insert(const Uni *p) {
    Uni d = uni_derivative(p), g = uni_gcd(*p, d), s, rest;
    if (failure || !uni_divide(p, &g, &s)) { fail(SIGN_LIMIT); return; }
    uni_primitive(&s);
    if (s.c[s.degree] < 0) uni_negate(&s);
    for (int i = 0; i < sign_bases && s.degree > 0 && !failure; i++) {
        g = uni_gcd(s, sign_base[i]);
        if (g.degree <= 0) continue;
        if (!uni_divide(&sign_base[i], &g, &rest)) { fail(SIGN_LIMIT); return; }
        if (rest.degree > 0) {
            if (rest.c[rest.degree] < 0) uni_negate(&rest);
            sign_base[i] = rest;
            base_append(g);
        }
        if (!uni_divide(&s, &g, &rest)) { fail(SIGN_LIMIT); return; }
        s = rest;
        if (s.degree >= 0 && s.c[s.degree] < 0) uni_negate(&s);
    }
    if (s.degree > 0 && !failure) base_append(s);
}

/* Aggiunge ai punti il razionale value. */
static void point_exact(Wide value) {
    if (sign_points_count == MAX_POINTS) { fail("troppi punti nella tabella dei segni"); return; }
    sign_point[sign_points_count++] = (Critical){1, value, value, -1, -1};
}

/* 18p-3. Aggiunge ai punti le radici di sign_base[element] tra low e high,
 * che sono `roots`, dimezzando l'intervallo finché ne contiene una sola. La
 * catena di Sturm è già quella dell'elemento, che non ha radici razionali:
 * il punto medio non è mai una radice. */
static void point_isolate(int element, Wide low, Wide high, int roots) {
    if (roots <= 0 || failure) return;
    if (roots == 1) {
        if (sign_points_count == MAX_POINTS) { fail("troppi punti nella tabella dei segni"); return; }
        sign_point[sign_points_count++] = (Critical){0, low, high, element, -1};
        return;
    }
    Wide mid = wide_mid(low, high);
    int left = sturm_changes(low) - sturm_changes(mid);
    point_isolate(element, low, mid, left);
    point_isolate(element, mid, high, roots - left);
}

/* Dimezza l'intervallo del punto p, che non è esatto, tenendo la metà che
 * contiene la radice: quella ai cui estremi il polinomio ha segni opposti,
 * perché la radice è semplice. */
static void point_refine(Critical *p) {
    /* Un punto che non è radice di un polinomio non si può stringere. */
    if (p->element < 0) return;
    Wide mid = wide_mid(p->low, p->high);
    const Uni *b = &sign_base[p->element];
    if (uni_sign_at(b, mid) == uni_sign_at(b, p->low)) p->low = mid; else p->high = mid;
}

/* Confronto tra punti per qsort, valido quando gli intervalli non si
 * toccano: decide l'estremo inferiore. */
static int point_order(const void *a, const void *b) {
    return wide_cmp(((const Critical *)a)->low, ((const Critical *)b)->low);
}

/* Ritorna un intero che supera in valore assoluto ogni radice reale di p,
 * che non è costante.
 *
 * Limite di Fujiwara. Sia d il grado, e B tale che per ogni i < d valga
 * |c_i| <= |c_d| (B/2)^{d-i}. Se |x| >= B allora
 *
 *     |c_i x^i| <= |c_d| (B/2)^{d-i} |x|^i <= |c_d| |x|^d / 2^{d-i},
 *
 * e sommando su i < d si resta sotto |c_d x^d| (1/2 + 1/4 + ...): il termine
 * di grado più alto non può essere compensato, quindi x non è una radice.
 * Rispetto al limite di Cauchy, 1 + max |c_i / c_d|, questo tiene conto dei
 * gradi: per x^8 + 10^8 dà 32 invece di cento milioni, e i conti nei punti
 * estremi restano piccoli. Si prova B = 2, 4, 8, ... */
static Wide uni_bound(const Uni *p) {
    __int128 lead = p->c[p->degree] < 0 ? -p->c[p->degree] : p->c[p->degree];
    for (__int128 half = 1; ; half *= 2) {
        int enough = 1;
        for (int i = 0; i < p->degree && enough; i++) {
            /* |c_i| <= lead * half^(d-i)? Se il prodotto esce dai 128 bit è
             * certamente abbastanza grande. */
            __int128 size = p->c[i] < 0 ? -p->c[i] : p->c[i], right = lead;
            for (int k = 0; k < p->degree - i && right < size; k++)
                if (__builtin_mul_overflow(right, half, &right)) right = size;
            enough = right >= size;
        }
        if (enough) return (Wide){2 * half + 1, 1};
        if (half > ((__int128)1 << 100)) { fail(SIGN_LIMIT); return (Wide){1, 1}; }
    }
}

/* Mette in list[], che ha `room` posti, i divisori positivi di value, che
 * non è zero, e ne ritorna il numero; -1 se non ci stanno. */
static int divisors_of(long long value, long long *list, int room) {
    int count = 0;
    if (value < 0) value = -value;
    for (long long d = 1; d <= value; d++) {
        if (value % d) continue;
        if (count == room) return -1;
        list[count++] = d;
    }
    return count;
}

/* 18p-6. Cerca un fattore di secondo grado, a coefficienti interi, di p, che
 * ha coefficienti interi senza divisori comuni e nessuna radice razionale.
 * Se lo trova lo mette in *factor, mette il quoziente in *rest e ritorna 1.
 *
 * A che cosa serve. La base separa le radici di polinomi diversi, ma non
 * scompone un polinomio: (x^2 - 2)(x^2 + 3) resta x^4 + x^2 - 6, e le sue
 * radici reali si potrebbero indicare solo con un nome. Trovato il fattore
 * x^2 - 2 si scrivono come sui libri: -\sqrt{2} e \sqrt{2}.
 *
 * Metodo di Kronecker. Se q, a coefficienti interi senza divisori comuni,
 * divide p, il quoziente ha coefficienti interi (lemma di Gauss); quindi per
 * ogni intero t il numero q(t) divide p(t). Un polinomio di secondo grado
 * A x^2 + B x + C è determinato dai valori in tre punti; con 0, 1 e -1:
 *
 *     q(0) = C,    q(1) = A + B + C,    q(-1) = A - B + C,
 *
 * cioè A = (q(1) + q(-1)) / 2 - C e B = (q(1) - q(-1)) / 2. Si provano tutte
 * le terne di divisori di p(0), p(1) e p(-1), che non sono zero perché p non
 * ha radici razionali, e ogni candidato si controlla con una divisione. Le
 * terne sono in numero finito, quindi la ricerca è completa: se non trova
 * nulla, p non ha fattori di secondo grado. q e -q sono lo stesso fattore:
 * basta C positivo.
 *
 * Con valori oltre KRONECKER_LIMIT, o con più di KRONECKER_DIVISORS divisori,
 * non cerca: non è un errore, le radici avranno un nome. */
int uni_quadratic_factor(const Uni *p, Uni *factor, Uni *rest) {
    long long at[3] = {0, 0, 0}, list[3][KRONECKER_DIVISORS];
    int count[3];

    /* p(0), p(1) e p(-1), e i loro divisori. */
    for (int i = 0; i <= p->degree; i++) {
        if (p->c[i] > KRONECKER_LIMIT || p->c[i] < -KRONECKER_LIMIT) return 0;
        if (i == 0) at[0] = (long long)p->c[0];
        at[1] += (long long)p->c[i];
        at[2] += i % 2 ? -(long long)p->c[i] : (long long)p->c[i];
    }
    for (int i = 0; i < 3; i++) {
        if (at[i] == 0 || at[i] > KRONECKER_LIMIT || at[i] < -KRONECKER_LIMIT) return 0;
        count[i] = divisors_of(at[i], list[i], KRONECKER_DIVISORS);
        if (count[i] < 0) return 0;
    }

    /* Ogni terna, con i due segni per q(1) e q(-1). */
    for (int i = 0; i < count[0]; i++)
        for (int j = 0; j < 2 * count[1]; j++)
            for (int k = 0; k < 2 * count[2]; k++) {
                long long zero = list[0][i], plus = j % 2 ? -list[1][j / 2] : list[1][j / 2], minus = k % 2 ? -list[2][k / 2] : list[2][k / 2];
                if ((plus + minus) % 2 || (plus + minus) / 2 == zero) continue;
                *factor = (Uni){2, {zero, (plus - minus) / 2, (plus + minus) / 2 - zero}};
                uni_primitive(factor);
                if (uni_divide(p, factor, rest)) return 1;
                if (failure) return 0;
            }
    return 0;
}

/* Trova i punti della tabella: tutte le radici reali dei polinomi di
 * sign_poly[], ognuna una volta, in ordine crescente.
 *
 * Serve sapere con certezza quali radici sono razionali: perché nei numeri
 * razionali contano solo quelle, e perché tolte quelle nessun punto medio
 * può più essere una radice. Quando non si riesce a stabilirlo (coefficienti
 * troppo grandi per elencarne i divisori) annota un errore. */
static void sign_points(int where) {
    sign_bases = sign_points_count = 0;
    for (int i = 0; i < sign_polys && !failure; i++)
        if (sign_space[i] == where && sign_poly[i].degree > 0) base_insert(&sign_poly[i]);

    /* Un elemento alla volta: prima le radici razionali, che si tolgono,
     * poi quelle di ciò che resta, con Sturm. */
    for (int k = 0; k < sign_bases && !failure; k++) {
        Uni *b = &sign_base[k];
        long long c[MAX_UNIVARIATE + 1];
        Frac root[MAX_UNIVARIATE + 2];
        int small = b->degree <= MAX_UNIVARIATE, found = -1;
        if (b->degree == 1) { point_exact(wide_make(-b->c[0], b->c[1])); continue; }

        /* Quante radici reali ha in tutto: se nessuna, come x^2 + 1, non
         * serve altro. Gli estremi stanno oltre ogni radice (uni_bound),
         * quindi non sono radici. */
        Wide bound = uni_bound(b), minus = {-bound.num, 1};
        sturm_build(b);
        if (failure || sturm_changes(minus) - sturm_changes(bound) == 0) continue;

        /* Le radici razionali. */
        for (int i = 0; i <= b->degree && small; i++) {
            if (b->c[i] > LLONG_MAX / 4 || b->c[i] < -(LLONG_MAX / 4)) small = 0;
            else c[i] = (long long)b->c[i];
        }
        if (small) found = rational_roots(c, b->degree, root);
        if (found < 0) { fail("non riesco a stabilire quali radici di un polinomio sono razionali"); return; }
        for (int i = 0; i < found && !failure; i++) {
            Uni linear = {1, {-(__int128)root[i].num, root[i].den}}, rest;
            point_exact((Wide){root[i].num, root[i].den});
            if (!uni_divide(b, &linear, &rest)) { fail(SIGN_LIMIT); return; }
            *b = rest;
        }
        if (b->degree < 1 || failure) continue;

        /* 18p-6. I fattori di secondo grado diventano elementi a sé, in
         * fondo alla base: questo ciclo arriverà anche a loro. Un polinomio
         * di terzo grado senza radici razionali non ne ha. */
        Uni quadratic, rest;
        while (!failure && b->degree >= 4 && uni_quadratic_factor(b, &quadratic, &rest)) {
            base_append(quadratic);
            *b = rest;
        }
        if (failure) return;

        /* Le altre, che sono irrazionali. */
        bound = uni_bound(b);
        minus = (Wide){-bound.num, 1};
        sturm_build(b);
        point_isolate(k, minus, bound, sturm_changes(minus) - sturm_changes(bound));
    }

    /* I punti che non sono radici di polinomi, nella tabella della
     * variabile: ognuno con due razionali che lo chiudono, un passo di
     * griglia più in là dei due estremi del suo intervallo. */
    for (int i = 0; i < sign_polys && where < 0 && !failure; i++) {
        if (sign_kappa[i] < 0) continue;
        Range value = kappa[sign_kappa[i]].value;
        if (sign_points_count == MAX_POINTS || value.low < -1e9 || value.high > 1e9) { fail("troppi punti nella tabella dei segni"); return; }
        __int128 grid = (__int128)1 << 40, low = (__int128)(value.low * (double)grid) - 1, high = (__int128)(value.high * (double)grid) + 1;
        sign_point[sign_points_count++] = (Critical){0, wide_make(low, grid), wide_make(high, grid), -1, sign_kappa[i]};
    }

    /* Finché due intervalli si toccano si dimezza uno dei due che non sia un
     * punto esatto. Le radici sono numeri diversi, quindi finisce; due punti
     * che non sono radici e che non si riesce a separare fermano il conto. */
    for (int again = 1, rounds = 0; again && !failure; rounds++) {
        again = 0;
        if (rounds > 200) { fail(SIGN_LIMIT); return; }
        for (int i = 0; i < sign_points_count && !failure; i++)
            for (int j = i + 1; j < sign_points_count && !failure; j++) {
                Critical *p = &sign_point[i], *q = &sign_point[j];
                if (wide_cmp(p->high, q->low) < 0 || wide_cmp(q->high, p->low) < 0) continue;
                again = 1;
                if (!p->exact) point_refine(p);
                if (!q->exact) point_refine(q);
            }
    }

    /* Gli intervalli che isolano le radici irrazionali si stringono fino a
     * meno di un ottavo: non serve alla decisione, ma "la radice tra 5/4 e
     * 11/8" dice al lettore dov'è, "tra -3 e 3" no. Non di più, perché ogni
     * dimezzamento raddoppia i denominatori dei conti nei punti medi. */
    for (int i = 0; i < sign_points_count && !failure; i++) {
        Critical *p = &sign_point[i];
        __int128 gap, scale;
        while (!failure && !p->exact && p->element >= 0) {
            /* high - low = gap / scale, da confrontare con 1/8. */
            if (__builtin_mul_overflow(p->high.num, p->low.den, &gap) || __builtin_mul_overflow(p->low.num, p->high.den, &scale) ||
                __builtin_sub_overflow(gap, scale, &gap) || __builtin_mul_overflow(gap, (__int128)8, &gap) ||
                __builtin_mul_overflow(p->high.den, p->low.den, &scale)) { fail(SIGN_LIMIT); break; }
            if (gap < scale) break;
            point_refine(p);
        }
    }
    if (!failure) qsort(sign_point, (size_t)sign_points_count, sizeof *sign_point, point_order);
}

/* =============================================================================
 * 18.9 LE LETTERE DELLA TABELLA: ESPONENZIALI, LOGARITMI, FUNZIONI
 *      GONIOMETRICHE, FAMIGLIE
 * ============================================================================
 *
 * Ciò che non è una frazione di polinomi nella variabile lo diventa in
 * un'altra lettera: un esponenziale o un logaritmo (18p-8) è la lettera di
 * uno "spazio", una funzione goniometrica è una frazione in t = tan(u / 2)
 * (18p-11), una famiglia di soluzioni x = a + k T è un angolo (18p-13). Qui
 * si riconoscono queste forme e si registrano le lettere; eval() le usa
 * attraverso gli agganci dichiarati prima di eval_call() (capitolo 11). I
 * segni nelle lettere li calcola l'albero dei segni, nel capitolo 18.10.
 *
 * 18p-8. ESPONENZIALI E LOGARITMI
 *
 * 5^(x+2) - 4 * 5^(1-x) - 30 non è un polinomio in x, ma lo è nella lettera
 * t = 5^x: 25 t - 20 / t - 30. E il segno di un polinomio in t dipende solo
 * da dove sta t rispetto alle sue radici. Qui sta tutto il metodo: la
 * funzione t = 5^x cresce, quindi "t è sopra la radice r" vuol dire
 * "x è sopra log_5 r", che è un confronto nella x.
 *
 *   - Uno "spazio" è una funzione crescente della variabile trattata come
 *     lettera: p^(x/L) per un primo p (una potenza b^(a x + c) è un prodotto
 *     di potenze intere di queste lettere, per un numero), oppure log_b f(x)
 *     con b > 1 (un logaritmo in base minore di 1 è l'opposto di uno in base
 *     maggiore).
 *   - I "gradini" dello spazio sono le radici reali dei polinomi nella sua
 *     lettera, trovate come nella tabella (18p-3, 18p-4), in ordine.
 *   - Per ogni gradino r, il confronto "lettera - r" nella variabile:
 *       p^(x/L) - r   ha il segno di   x - L log_p r   (r > 0; se r <= 0
 *                                       l'esponenziale gli sta sempre sopra);
 *       log_b f - r   ha il segno di   f(x) - b^r.
 *     Se log_p r è un intero, o b^r un razionale o una radice quadrata, è un
 *     confronto che la tabella tratta già. Altrimenti x - L log_p r si
 *     annulla in un numero che non è radice di nessun polinomio a
 *     coefficienti razionali: entra nella tabella come punto a sé (Kappa), e
 *     il suo posto tra gli altri punti lo decidono gli intervalli del
 *     capitolo 24.
 *   - In una riga della tabella, contando i gradini che la lettera ha sotto
 *     di sé si sa in quale tratto si trova, e il segno di ogni polinomio su
 *     quel tratto si calcola in un punto razionale del tratto.
 *
 * Due casi si risolvono senza gradini. Una somma di logaritmi nella stessa
 * base con coefficienti razionali, più un numero, ha il segno di un
 * prodotto di potenze degli argomenti meno una potenza della base
 * (sign_log_linear()): è la regola "la somma dei logaritmi è il logaritmo
 * del prodotto", che vale dove gli argomenti sono positivi, cioè dove il
 * confronto ha un valore. E un polinomio in più lettere che è un prodotto
 * di polinomi in lettere diverse, come (2^x - 1)(5^x - 1), ha il segno del
 * prodotto dei segni (sign_ground()).
 *
 * Altre tre regole portano a queste forme ciò che è scritto in un altro
 * modo. La radice di un prodotto di esponenziali si estrae (exp_root()):
 * \sqrt[3]{11^{9x}} è 11^{3x}. Il logaritmo di una potenza, accanto al
 * logaritmo della base nello stesso confronto, è un suo multiplo
 * (alias_collect()). E un polinomio i cui termini sono potenze di uno
 * stesso rapporto di esponenziali, come 2 \cdot 4^x - 5 \cdot 6^x + 3 \cdot 9^x,
 * è un polinomio in quel rapporto (sign_one_ratio()).
 *
 * Che cosa resta fuori: la variabile sia all'esponente sia fuori senza che
 * il polinomio si spezzi (x + 2^x), esponenti non di primo grado, un
 * logaritmo o un rapporto di esponenziali uguale a un numero irrazionale
 * che non so scrivere, somme di logaritmi in basi diverse. Il programma lo
 * dice.
 */

/* Ritorna lo spazio dell'esponenziale di base il primo prime (0: il numero
 * e), creandolo se create non è zero; NULL se non c'è, o non c'è più posto. */
static Space *space_exp(long long prime, int create) {
    for (int s = 0; s < spaces; s++)
        if (space[s].kind == SPACE_EXP && space[s].prime == prime) return &space[s];
    if (!create || spaces == MAX_SPACES) return NULL;
    Space *sp = &space[spaces];
    memset(sp, 0, sizeof *sp);
    sp->kind = SPACE_EXP;
    sp->prime = prime;
    sp->scale = 1;
    sp->letter = atom_var(SURD_NAMES + MAX_SURDS + spaces++);
    return sp;
}

/* Ritorna il numero dello spazio del logaritmo in base base (o in base e,
 * se natural) dell'espressione argument, creandolo se create non è zero; -1
 * se non c'è, o non c'è più posto. Due logaritmi sono lo stesso spazio se
 * hanno la stessa base e l'argomento scritto allo stesso modo. */
static int space_log(Frac base, int natural, const Node *argument, int create) {
    for (int s = 0; s < spaces; s++)
        if (space[s].kind == SPACE_LOG && space[s].natural == natural && (natural || frac_cmp(space[s].base, base) == 0) && node_equal(space[s].argument, argument)) return s;
    if (!create || spaces == MAX_SPACES) return -1;
    Space *sp = &space[spaces];
    memset(sp, 0, sizeof *sp);
    sp->kind = SPACE_LOG;
    sp->base = base;
    sp->natural = natural;
    sp->argument = argument;
    sp->letter = atom_var(SURD_NAMES + MAX_SURDS + spaces);
    return spaces++;
}

/* Ritorna il numero dello spazio di cui l'atomo è la lettera, oppure
 * `spaces` se non è la lettera di nessuno spazio. */
static int space_of(int atom) {
    int s = 0;
    while (s < spaces && space[s].letter != atom) s++;
    return s;
}

/* Legge la base di una potenza o di un logaritmo. Ritorna 1 se node è il
 * numero e (*euler = 1), oppure un razionale positivo diverso da 1, che
 * mette in *value. La lettera e è il numero di Nepero quando non è la
 * variabile dell'enunciato né una variabile con un valore. */
static int constant_base(const Node *node, Frac *value, int *euler) {
    Num number;
    *euler = node->kind == N_VAR && node->name == 'e' && sign_name != 'e' && !env_lookup('e');
    if (*euler) return 1;
    if (node_uses_letter(node, sign_name)) return 0;
    Rat base = eval(node);
    if (failure || !rat_number(base, &number) || number.im.num != 0 || number.re.num <= 0 || number.re.num == number.re.den) return 0;
    *value = number.re;
    return 1;
}

/* Ritorna la radice m-esima intera di v > 0, o 0 se v non è una potenza
 * m-esima esatta. */
static long long exact_root(long long v, int m) {
    long long low = 1, high = v;
    while (low < high) {
        long long middle = low + (high - low) / 2, power = 1;
        for (int i = 0; i < m && power <= v; i++) power = power > v / middle ? v + 1 : power * middle;
        if (power < v) low = middle + 1; else high = middle;
    }
    long long power = 1;
    for (int i = 0; i < m; i++) power = power > v / low ? v + 1 : power * low;
    return power == v ? low : 0;
}

/* Legge la base del logaritmo node (FN_LN o FN_LOG) e la porta a una forma
 * sola: maggiore di 1, e non potenza di un altro razionale. Mette in *value
 * la base così ridotta e in *factor il numero per cui va moltiplicato il
 * logaritmo nella base ridotta per avere quello scritto:
 *
 *     log_(1/b) f = -log_b f,        log_(b^m) f = (log_b f) / m.
 *
 * Così log_9, log_3 e log_(1/3) dello stesso argomento sono multipli della
 * stessa lettera. Per il logaritmo naturale *euler = 1 e il fattore è 1. */
static int log_base(const Node *node, Frac *value, int *euler, Frac *factor) {
    *factor = frac_int(1);
    *euler = node->op == FN_LN;
    if (*euler) return 1;
    if (!node->b || !constant_base(node->b, value, euler)) return 0;
    if (*euler) return 1;
    if (value->num < value->den) {
        *value = (Frac){value->den, value->num};
        *factor = frac_int(-1);
    }
    for (int m = 40; m >= 2; m--) {
        long long top = exact_root(value->num, m), bottom = exact_root(value->den, m);
        if (!top || !bottom) continue;
        *value = (Frac){top, bottom};
        *factor = frac_div(*factor, frac_int(m));
        break;
    }
    return 1;
}

/* Il più piccolo multiplo comune di due interi positivi. */
long long lcm_small(long long a, long long b) { return a / (long long)gcd128(a, b) * b; }

/* Registra gli spazi che servono all'espressione node: uno per ogni primo
 * della base di una potenza con la variabile all'esponente, uno per ogni
 * logaritmo con la variabile nell'argomento. Per gli esponenziali fissa
 * anche L, il più piccolo intero per cui ogni potenza è una potenza intera
 * di p^(x/L). Ciò che non ha la forma attesa viene lasciato stare: sarà il
 * conto vero a dire che non è trattato. */
static void space_collect(const Node *node) {
    Frac base, alpha, beta, factor;
    int euler;
    long long prime, times;
    if (!node || failure) return;
    space_collect(node->a);
    space_collect(node->b);
    space_collect(node->c);
    if (node->kind == N_POW && node_uses_letter(node->b, sign_name) && constant_base(node->a, &base, &euler) &&
        rat_affine_in(eval(node->b), sign_x, &alpha, &beta)) {
        Space *sp = euler ? space_exp(0, 1) : NULL;
        if (sp) sp->scale = lcm_small(sp->scale, alpha.den);
        for (int side = 0; side < 2 && !euler; side++) {
            long long value = side ? base.den : base.num;
            while (pop_prime(&value, &prime, &times)) {
                sp = space_exp(prime, 1);
                if (sp) sp->scale = lcm_small(sp->scale, frac_mul(alpha, frac_int(times)).den);
            }
        }
    }
    if (node->kind == N_CALL && (node->op == FN_LN || node->op == FN_LOG) && node_uses_letter(node->a, sign_name) && log_base(node, &base, &euler, &factor))
        space_log(base, euler, node->a, 1);
}

/* Dopo space_collect(): per ogni radice di node il cui radicando è un
 * prodotto di potenze di lettere di esponenziali, allarga L quanto basta
 * perché ogni esponente sia un multiplo dell'indice, così che la radice si
 * possa estrarre (exp_root()): con \sqrt{2^{x}} la lettera diventa
 * 2^(x/2). Lo si fa solo per queste radici, e dalle più interne: allargare
 * L per una radice come \sqrt{e^{x} - 6} renderebbe irrazionale, senza
 * motivo, il gradino e^x = 6. */
static void root_scales(const Node *node) {
    if (!node) return;
    root_scales(node->a);
    root_scales(node->b);
    root_scales(node->c);
    if (node->kind != N_CALL || node->op != FN_ROOT || !node->b || node->b->kind != N_NUM || node->b->value < 2 || node->b->value > 40) return;
    Rat r = eval(node->a);
    int plain = !failure && r.num.count == 1 && r.den.count == 1;
    failure = NULL;
    for (int side = 0; side < 2 && plain; side++) {
        const Term *term = side ? &r.den.term[0] : &r.num.term[0];
        for (int f = 0; f < term->mono.count; f++) {
            Frac e = term->mono.factor[f].exp;
            int s = space_of(term->mono.factor[f].atom);
            if (s == spaces || space[s].kind != SPACE_EXP || e.den != 1) return;
        }
    }
    for (int side = 0; side < 2 && plain; side++) {
        const Term *term = side ? &r.den.term[0] : &r.num.term[0];
        for (int f = 0; f < term->mono.count; f++) {
            long long e = term->mono.factor[f].exp.num, index = node->b->value;
            space[space_of(term->mono.factor[f].atom)].scale *= index / (long long)gcd128(e < 0 ? -e : e, index);
        }
    }
}

/* Chiama visit sui due membri di ogni confronto della condizione f. */
static void formula_sides(const Formula *f, void (*visit)(const Node *)) {
    if (!f) return;
    if (f->kind == F_EQUAL || f->kind == F_DISTINCT || f->kind == F_LESS || f->kind == F_LESS_EQ) {
        visit(f->left);
        visit(f->right);
        return;
    }
    formula_sides(f->a, visit);
    formula_sides(f->b, visit);
}

/* Registra gli spazi di tutti i confronti della condizione f; poi allarga
 * quelli che servono alle radici di prodotti di esponenziali. */
static void formula_spaces(const Formula *f) {
    formula_sides(f, space_collect);
    formula_sides(f, root_scales);
}

/* 18p-8. Se node, una potenza, ha la variabile all'esponente, una base
 * numerica positiva e l'esponente di primo grado a x + c con c intero, mette
 * in *out il suo valore nelle lettere degli spazi e ritorna 1:
 *
 *     b^(a x + c) = b^c * prodotto sui primi p di b di (p^(x/L))^(e_p a L),
 *
 * dove e_p è l'esponente di p nella scomposizione di b. Le divisioni di
 * questo conto non pongono condizioni: una potenza di un numero positivo non
 * è mai zero. */
int exp_letters(const Node *node, Rat *out) {
    Frac base, alpha, beta;
    int euler, done = 1, listed = conditions_on;
    long long prime, times;
    if (!space_live || !node_uses_letter(node->b, sign_name) || !constant_base(node->a, &base, &euler)) return 0;
    if (!rat_affine_in(eval(node->b), sign_x, &alpha, &beta) || beta.den != 1 || (euler && beta.num != 0)) return 0;
    conditions_on = 0;
    if (euler) {
        /* La base e: una lettera sola, e nessun numero davanti. */
        Space *sp = space_exp(0, 0);
        Frac power = sp ? frac_mul(alpha, frac_int(sp->scale)) : frac_int(0);
        done = sp && power.den == 1;
        if (done) *out = rat_pow_int(rat_atom(sp->letter), power.num);
    } else {
        *out = rat_pow_int(rat_frac(base), beta.num);
    }
    for (int side = 0; side < 2 && done && !euler; side++) {
        long long value = side ? base.den : base.num;
        while (done && pop_prime(&value, &prime, &times)) {
            Space *sp = space_exp(prime, 0);
            Frac power = sp ? frac_mul(frac_mul(alpha, frac_int(side ? -times : times)), frac_int(sp->scale)) : frac_int(0);
            if (!sp || power.den != 1) done = 0;
            else *out = rat_mul(*out, rat_pow_int(rat_atom(sp->letter), power.num));
        }
    }
    conditions_on = listed;
    return done && !failure;
}

/* 18p-8. Vedi la dichiarazione prima di eval_call(). r deve essere un
 * razionale positivo per un prodotto di potenze, anche negative, di lettere
 * di esponenziali; la radice si estrae se il razionale è una potenza
 * index-esima esatta e ogni esponente è un multiplo di index. Le lettere
 * sono positive: la radice n-esima di c g^(n a) è la radice di c per g^a,
 * senza valori assoluti e senza condizioni. È così che \sqrt[3]{11^{9x}}
 * diventa 11^{3x}. Un numero senza lettere resta alla regola di sempre. */
int exp_root(Rat r, long long index, Rat *out) {
    int letters = 0;
    if (!space_live || spaces == 0 || failure || index > 40 || r.num.count != 1 || r.den.count != 1) return 0;
    const Term *top = &r.num.term[0], *bottom = &r.den.term[0];
    if (top->coef.im.num != 0 || bottom->coef.im.num != 0) return 0;
    Frac coefficient = frac_div(top->coef.re, bottom->coef.re);
    long long up = coefficient.num > 0 ? exact_root(coefficient.num, (int)index) : 0, down = exact_root(coefficient.den, (int)index);
    if (failure || !up || !down) return 0;
    *out = rat_frac((Frac){up, down});
    for (int side = 0; side < 2; side++) {
        const Term *term = side ? bottom : top;
        for (int f = 0; f < term->mono.count; f++) {
            Frac e = term->mono.factor[f].exp;
            int s = space_of(term->mono.factor[f].atom);
            if (s == spaces || space[s].kind != SPACE_EXP || e.den != 1 || e.num % index != 0) return 0;
            *out = rat_mul(*out, rat_pow_int(rat_atom(space[s].letter), (side ? -e.num : e.num) / index));
            letters++;
        }
    }
    return letters > 0 && !failure;
}

/* 18p-8. Il logaritmo di una potenza accanto al logaritmo della base.
 *
 * log_b(B^n) = n log_b(B) vale dove B è positivo. Dove B è negativo e n è
 * pari il primo membro ha un valore e il secondo no: per questo \log x^{2}
 * e \log x sono due lettere diverse. Ma un confronto in cui compare anche
 * log_b(B) ha un valore solo dove B è positivo, e lì i due logaritmi sono
 * legati: dentro quel confronto log_b(B^n) si scrive n volte la lettera di
 * log_b(B). È ciò che serve a (\log x^{2})^{2} + 4\log x = 0, che così è un
 * polinomio in una lettera sola. Senza log_b(B) nello stesso confronto la
 * regola non si applica.
 *
 * alias_node[i] è un logaritmo di una potenza del confronto che si sta
 * preparando, alias_space[i] lo spazio del logaritmo della base e
 * alias_power[i] l'esponente n. Li riempie alias_collect(), li usa
 * log_letter(), e sign_prepare() li azzera alla fine del confronto. */
#define MAX_LOG_ALIAS 8
static const Node *alias_node[MAX_LOG_ALIAS];
static int alias_space[MAX_LOG_ALIAS], aliases;
static long long alias_power[MAX_LOG_ALIAS];

/* Ritorna 1 se in node compare un logaritmo con la base ridotta base (o in
 * base e, se natural) e l'argomento scritto come argument. */
static int log_present(const Node *node, Frac base, int natural, const Node *argument) {
    Frac found, factor;
    int euler;
    if (!node) return 0;
    if (node->kind == N_CALL && (node->op == FN_LN || node->op == FN_LOG) && node_equal(node->a, argument) && log_base(node, &found, &euler, &factor) &&
        euler == natural && (natural || frac_cmp(found, base) == 0)) return 1;
    return log_present(node->a, base, natural, argument) || log_present(node->b, base, natural, argument) || log_present(node->c, base, natural, argument);
}

/* Registra in alias_node[] i logaritmi di potenze di node, un pezzo del
 * confronto f, che in f stanno accanto al logaritmo della loro base. */
static void alias_collect(const Node *node, const Formula *f) {
    Frac base, factor;
    int euler;
    if (!node) return;
    alias_collect(node->a, f);
    alias_collect(node->b, f);
    alias_collect(node->c, f);
    if (node->kind != N_CALL || (node->op != FN_LN && node->op != FN_LOG) || node->a->kind != N_POW || node->a->b->kind != N_NUM || node->a->b->value < 2) return;
    if (aliases == MAX_LOG_ALIAS || !node_uses_letter(node->a->a, sign_name) || !log_base(node, &base, &euler, &factor)) return;
    int s = space_log(base, euler, node->a->a, 0);
    if (s < 0 || (!log_present(f->left, base, euler, node->a->a) && !log_present(f->right, base, euler, node->a->a))) return;
    alias_node[aliases] = node;
    alias_space[aliases] = s;
    alias_power[aliases++] = node->a->b->value;
}

/* 18p-8. Se node, un logaritmo, ha la variabile nell'argomento e uno spazio
 * registrato, mette in *out la lettera dello spazio, moltiplicata per il
 * fattore che porta dalla base ridotta a quella scritta (log_base()), e
 * ritorna 1. Annota in space_seen che il confronto in corso contiene quel
 * logaritmo: l'argomento dovrà essere positivo. */
int log_letter(const Node *node, Rat *out) {
    Frac base, factor;
    int euler;
    if (!space_live || !node_uses_letter(node->a, sign_name) || !log_base(node, &base, &euler, &factor)) return 0;
    int s = space_log(base, euler, node->a, 0);
    for (int i = 0; i < aliases; i++) {
        if (alias_node[i] != node) continue;
        s = alias_space[i];
        factor = frac_mul(factor, frac_int(alias_power[i]));
    }
    if (s < 0) return 0;
    space_seen |= 1u << s;
    *out = rat_mul(rat_frac(factor), rat_atom(space[s].letter));
    return 1;
}

/* 18p-11. FUNZIONI GONIOMETRICHE
 *
 * 2 \sin x \cos x > \frac{1}{2} non è un confronto tra frazioni in x. Lo
 * diventa con la sostituzione della tangente dell'angolo metà:
 *
 *     t = tan(u / 2),     sin u = 2t / (1 + t^2),     cos u = (1 - t^2) / (1 + t^2).
 *
 * Le due formule sono identità (si verificano scrivendo seno e coseno di
 * u = 2 (u/2) con le formule di duplicazione e dividendo per
 * cos^2(u/2) + sin^2(u/2) = 1). Quando u percorre un giro, da -pi a pi
 * esclusi, t percorre tutta la retta reale una volta sola, crescendo: la
 * tabella dei segni nella lettera t descrive quindi tutto un periodo. Resta
 * fuori un punto solo, u = pi, dove t non ha un valore: lì seno e coseno
 * valgono 0 e -1, e l'enunciato si calcola a parte.
 *
 * Gli argomenti. Ogni funzione goniometrica dell'enunciato deve avere
 * l'argomento a x + b pi, con a e b razionali. Si prende u = g x, dove g è
 * il più grande razionale di cui tutti gli a sono multipli interi: allora
 * a x + b pi = n u + b pi con n intero, e
 *
 *   - cos(n u) + i sin(n u) = (cos u + i sin u)^n (formula di De Moivre):
 *     n moltiplicazioni tra numeri complessi danno cos(n u) e sin(n u) come
 *     frazioni in t;
 *   - cos(b pi) e sin(b pi) sono numeri noti quando b pi è un multiplo di
 *     15 gradi: si scrivono con le radici di 2 e di 3 (trig_constant());
 *   - le formule di addizione mettono insieme le due cose.
 *
 * Tangente e cotangente sono i due quozienti, e dove il denominatore è zero
 * non hanno un valore: lo dice la divisione, come sempre.
 *
 * Che cosa resta fuori: la variabile anche fuori dalle funzioni
 * goniometriche (x + sin x), salvo che in un confronto con un multiplo di pi
 * che restringe la condizione a un intervallo (18p-14); argomenti non di
 * primo grado; angoli costanti che non sono multipli di 15 gradi; angoli
 * multipli così alti che i polinomi in t escono dall'aritmetica esatta
 * della tabella (cos x + cos 3x = 2 sin 6x cos x).
 */

/* Lo stato dell'enunciato periodico in corso. trig_on dice che lo è;
 * trig_live che si sta preparando un suo confronto (solo allora le funzioni
 * diventano frazioni in t); trig_at_pi che le si vuole nel punto u = pi
 * invece che in t; trig_x e trig_letter sono gli atomi della variabile e di
 * t; trig_scale è g; trig_bad dice che una funzione ha un argomento non
 * trattato. trig_root[] sono i nodi di radice di 2 e di radice di 3, che
 * servono a scrivere seni e coseni dei multipli di 15 gradi. */
int trig_on, trig_live, trig_at_pi, trig_bad;
static int trig_x, trig_letter;
static Frac trig_scale;
static Node *trig_root[2];

/* Le finestre dell'enunciato periodico in corso (18p-14): quante sono, il
 * più basso e il più alto dei giri in cui cade un loro estremo, il primo e
 * l'ultimo giro da leggere, e il giro che si sta leggendo. Senza finestre
 * si legge un giro solo, il numero 0. */
static int windows;
static long long window_low, window_high, window_first, window_last, window_turn;

/* Se e = a x + b pi, con x la variabile dell'enunciato periodico, mette a
 * in *slope e b in *turn e ritorna 1. */
static int trig_affine(Rat e, Frac *slope, Frac *turn) {
    int pi = atom_var(VAR_PI);
    *slope = *turn = frac_int(0);
    if (failure || e.den.count != 1 || e.den.term[0].mono.count != 0 || e.den.term[0].coef.im.num != 0) return 0;
    for (int i = 0; i < e.num.count; i++) {
        const Term *t = &e.num.term[i];
        if (t->coef.im.num != 0 || t->mono.count != 1 || frac_cmp(t->mono.factor[0].exp, frac_int(1)) != 0) return 0;
        if (t->mono.factor[0].atom == trig_x) *slope = t->coef.re;
        else if (t->mono.factor[0].atom == pi) *turn = t->coef.re;
        else return 0;
    }
    *slope = frac_div(*slope, e.den.term[0].coef.re);
    *turn = frac_div(*turn, e.den.term[0].coef.re);
    return !failure;
}

/* 18p-13. LE FAMIGLIE x = a + k T
 *
 * Le soluzioni di una condizione periodica si scrivono con un intero k:
 * x = \frac{\pi}{6} + 2k\pi, oppure \frac{\pi}{6} + 2k\pi < x < \frac{5}{6}\pi + 2k\pi.
 * In un enunciato compaiono dentro un "esiste k intero", e dire che un
 * risultato così è giusto vuol dire confrontarlo con la condizione. Lo si
 * fa riportando anche lui a funzioni goniometriche di x. Si guarda l'angolo
 *
 *     A = 2 pi (x - a) / T,
 *
 * che fa un giro intero ogni volta che x avanza di un periodo T: tutta la
 * famiglia è descritta dal punto di angolo A sulla circonferenza.
 *
 *   - x = a + k T per qualche k esattamente quando A è un multiplo di 2 pi,
 *     cioè quando il punto è (1, 0): sin A = 0 e cos A > 0.
 *
 *   - a + k T <= x <= b + k T per qualche k, con 0 < b - a < T, esattamente
 *     quando il punto sta sull'arco che va dall'angolo 0 all'angolo
 *     D = 2 pi (b - a) / T. Con B = D - A = 2 pi (b - x) / T, l'angolo che
 *     manca alla fine dell'arco:
 *       - se l'arco è al più mezzo giro (D <= pi) i suoi punti interni sono
 *         quelli con sin A > 0 e sin B > 0: stanno nel semipiano a sinistra
 *         del raggio di partenza e in quello a destra del raggio di arrivo;
 *       - se è più di mezzo giro (D > pi) sono quelli con sin A > 0 oppure
 *         sin B > 0: il primo mezzo giro dopo la partenza e l'ultimo prima
 *         dell'arrivo, che insieme coprono l'arco perché si sovrappongono;
 *       - gli estremi sono i punti con A, o B, multiplo di 2 pi, come sopra,
 *         e contano se l'estremo è compreso.
 *
 * Una versione precedente usava l'angolo metà, sin(pi (x - a) / T): bastava
 * un seno per estremo, ma per una famiglia come \frac{\pi}{4} + 2k\pi
 * chiedeva il seno di pi/8, che non si scrive con le radici di 2 e di 3.
 * Con l'angolo intero servono i seni e i coseni di 2 pi a / T, e nei
 * risultati dei libri a è quasi sempre una frazione semplice del periodo.
 *
 * T deve essere un multiplo razionale di pi; a e b possono contenere, oltre
 * a multipli di pi, arcotangenti di razionali con coefficiente intero: dei
 * seni e dei coseni serve solo il segno, e cos(arctan m) e sin(arctan m)
 * stanno come 1 sta a m.
 */

/* Una famiglia: un pezzo di una condizione "esiste k intero". È un punto
 * per ogni k (single), x = low, oppure un intervallo per ogni k, da low a
 * high, con gli estremi compresi o no, a cui possono essere tolti i punti
 * x = hole[i]. low, high e hole[] sono espressioni in k. */
typedef struct {
    const Node *low, *high;               /* gli estremi; lo stesso nodo per un punto */
    int low_closed, high_closed, single;  /* 1 se l'estremo è compreso; 1 per un punto */
    const Node *hole[MAX_LATTICE_HOLES];  /* i punti tolti */
    int holes;                            /* quanti, in hole[] */
    int k;                                /* la lettera dell'intero */
} Family;

/* Legge il pezzo d di una condizione in name e nell'intero k, che deve
 * essere un confronto tra name e un'espressione, o una congiunzione di
 * confronti così: al più un estremo da ogni parte e alcuni punti tolti.
 * Aggiorna *out, che chi chiama ha azzerato, e ritorna 0 se d ha un'altra
 * forma. */
static int family_part(const Formula *d, int name, Family *out) {
    if (d->kind == F_AND) return family_part(d->a, name, out) && family_part(d->b, name, out);
    if (d->kind != F_EQUAL && d->kind != F_DISTINCT && d->kind != F_LESS && d->kind != F_LESS_EQ) return 0;
    int at_left = d->left->kind == N_VAR && d->left->name == name, at_right = d->right->kind == N_VAR && d->right->name == name;
    if (at_left == at_right) return 0;
    const Node *other = at_left ? d->right : d->left;
    if (d->kind == F_DISTINCT) {
        if (out->holes == MAX_LATTICE_HOLES) return 0;
        out->hole[out->holes++] = other;
    } else if (d->kind == F_EQUAL) {
        if (out->low || out->high) return 0;
        out->low = out->high = other;
        out->low_closed = out->high_closed = out->single = 1;
    } else if (at_right) {
        /* other < name: un estremo inferiore. */
        if (out->low) return 0;
        out->low = other;
        out->low_closed = d->kind == F_LESS_EQ;
    } else {
        if (out->high) return 0;
        out->high = other;
        out->high_closed = d->kind == F_LESS_EQ;
    }
    return 1;
}

/* Legge una famiglia dal pezzo d, come family_part(), e controlla che sia
 * completa: un punto, un intervallo con i suoi due estremi, oppure, quando
 * alone non è zero, un solo punto tolto (è il caso di "per ogni k,
 * x \neq ..."), che viene messo in low come se fosse un punto. */
static int family_read(const Formula *d, int name, int k, int alone, Family *out) {
    memset(out, 0, sizeof *out);
    out->k = k;
    if (!family_part(d, name, out)) return 0;
    if (alone) {
        if (out->low || out->high || out->holes != 1) return 0;
        out->low = out->high = out->hole[0];
        out->low_closed = out->high_closed = out->single = 1;
        out->holes = 0;
        return 1;
    }
    return out->low && out->high && (!out->single || out->holes == 0);
}

/* Se e = alpha + k tau pi, con k la lettera dell'intero e tau un razionale
 * diverso da zero, mette tau in *tau e alpha, che non contiene k, in *alpha,
 * e ritorna 1. */
static int family_period(const Node *e, int k, Frac *tau, Rat *alpha) {
    int letter = atom_var(k), pi = atom_var(VAR_PI);
    Rat value = eval(e);
    Poly rest = poly_const(num_int(0));
    *tau = frac_int(0);
    if (failure || value.den.count != 1 || value.den.term[0].mono.count != 0 || value.den.term[0].coef.im.num != 0) return 0;
    for (int i = 0; i < value.num.count; i++) {
        const Term *t = &value.num.term[i];
        Frac power = mono_exponent(&t->mono, letter);
        if (power.num == 0) { rest = poly_add(rest, poly_term(*t), 0); continue; }
        if (t->coef.im.num != 0 || t->mono.count != 2 || frac_cmp(power, frac_int(1)) != 0 || frac_cmp(mono_exponent(&t->mono, pi), frac_int(1)) != 0) return 0;
        *tau = frac_add(*tau, t->coef.re);
    }
    *tau = frac_div(*tau, value.den.term[0].coef.re);
    *alpha = (Rat){rest, value.den};
    return tau->num != 0 && !failure;
}

/* Ritorna 1 se f è un quantificatore su un intero che la tabella tratta
 * come una foglia: "esiste k in Z" o "per ogni k in Z", su tutti gli
 * interi. */
static int family_owner(const Formula *f) {
    return (f->kind == F_EXISTS || f->kind == F_FORALL) && f->numbers.integers && !f->numbers.bounded && f->numbers.holes == 0;
}

/* Chiama visit(d, context) per ogni pezzo della condizione f di un
 * quantificatore su un intero: i termini di una disgiunzione per "esiste",
 * quelli di una congiunzione per "per ogni". */
static void family_each(const Formula *owner, const Formula *f, void (*visit)(const Formula *, const Formula *, void *), void *context) {
    if (f->kind == (owner->kind == F_EXISTS ? F_OR : F_AND)) {
        family_each(owner, f->a, visit, context);
        family_each(owner, f->b, visit, context);
        return;
    }
    visit(owner, f, context);
}

/* Aggiorna trig_scale con la pendenza positiva slope di un angolo
 * dell'enunciato: trig_scale diventa il più grande razionale di cui sono
 * multipli interi tutte le pendenze viste, cioè il loro massimo comun
 * divisore (quello di due frazioni p/q e r/s è mcd(p s, r q) / (q s)). La
 * prima pendenza, con trig_scale ancora zero, è il valore di partenza. */
static void trig_scale_include(Frac slope) {
    if (trig_scale.num == 0) trig_scale = slope;
    else trig_scale = frac_make(gcd128((__int128)trig_scale.num * slope.den, (__int128)slope.num * trig_scale.den), (__int128)trig_scale.den * slope.den);
}

/* Per formula_trig(): aggiorna trig_scale con il periodo del pezzo d, o
 * mette 1 in trig_bad se il pezzo non è una famiglia trattata. Ogni
 * espressione della famiglia deve avere lo stesso tau, e la pendenza
 * 2 pi / T = 2 / tau dell'angolo A entra nel conto come quella di un
 * argomento. */
static void family_scale(const Formula *owner, const Formula *d, void *context) {
    Family family;
    Frac tau, other;
    Rat alpha;
    (void)context;
    if (!family_read(d, sign_name, owner->variable, owner->kind == F_FORALL, &family) || !family_period(family.low, family.k, &tau, &alpha)) { trig_bad = 1; return; }
    if (tau.num < 0) tau.num = -tau.num;
    const Node *more[1 + MAX_LATTICE_HOLES] = {family.high, family.hole[0], family.hole[1]};
    for (int i = 0; i < 1 + family.holes; i++) {
        if (!family_period(more[i], family.k, &other, &alpha)) { trig_bad = 1; return; }
        if (other.num < 0) other.num = -other.num;
        if (frac_cmp(other, tau) != 0) { trig_bad = 1; return; }
    }
    trig_scale_include(frac_div(frac_int(2), tau));
}

/* Registra le funzioni goniometriche dell'espressione node che contengono la
 * variabile: aggiorna trig_scale con le pendenze dei loro argomenti
 * (trig_scale_include()), e mette 1 in trig_bad se un argomento non è
 * a x + b pi. */
static void trig_collect(const Node *node) {
    Frac slope, turn;
    if (!node || failure) return;
    trig_collect(node->a);
    trig_collect(node->b);
    trig_collect(node->c);
    if (node->kind != N_CALL || node->op < FN_SIN || node->op > FN_COT || !node_uses_letter(node->a, sign_name)) return;
    if (!trig_affine(eval(node->a), &slope, &turn) || slope.num == 0) { trig_bad = 1; return; }
    if (slope.num < 0) slope.num = -slope.num;
    trig_scale_include(slope);
}

/* Registra le funzioni goniometriche di tutti i confronti della condizione f. */
static void formula_trig(const Formula *f) {
    if (!f) return;
    if (family_owner(f)) { family_each(f, f->a, family_scale, NULL); return; }
    if (f->kind == F_EQUAL || f->kind == F_DISTINCT || f->kind == F_LESS || f->kind == F_LESS_EQ) {
        trig_collect(f->left);
        trig_collect(f->right);
        return;
    }
    formula_trig(f->a);
    formula_trig(f->b);
}

/* Mette in *cosine e *sine il coseno e il seno di turn * pi, e ritorna 1;
 * 0 se l'angolo non è un multiplo di 15 gradi.
 *
 * L'angolo è k quarti di giro più r volte 15 gradi, con r da 0 a 5. Per il
 * resto valgono
 *
 *     cos 15 = (sqrt6 + sqrt2) / 4     sin 15 = (sqrt6 - sqrt2) / 4
 *     cos 30 = sqrt3 / 2               sin 30 = 1 / 2
 *     cos 45 = sin 45 = sqrt2 / 2,
 *
 * e 60 e 75 gradi sono i complementari di 30 e 15 (seno e coseno si
 * scambiano). Ogni quarto di giro in più manda (cos, sin) in (-sin, cos). */
static int trig_constant(Frac turn, Rat *cosine, Rat *sine) {
    Frac twelfths = frac_mul(turn, frac_int(12));
    if (twelfths.den != 1) return 0;
    long long steps = ((twelfths.num % 24) + 24) % 24, rest = steps % 6;
    Rat two = eval(trig_root[0]), three = eval(trig_root[1]), half = rat_frac((Frac){1, 2}), quarter = rat_frac((Frac){1, 4});
    Rat small = rat_mul(quarter, rat_add(rat_mul(two, three), two, 1)), large = rat_mul(quarter, rat_add(rat_mul(two, three), two, 0));
    Rat c[6] = {rat_int(1), large, rat_mul(half, three), rat_mul(half, two), half, small};
    Rat s[6] = {rat_int(0), small, half, rat_mul(half, two), rat_mul(half, three), large};
    *cosine = c[rest];
    *sine = s[rest];
    for (long long quarter_turns = steps / 6; quarter_turns > 0; quarter_turns--) {
        Rat was = *cosine;
        *cosine = rat_add(rat_int(0), *sine, 1);
        *sine = was;
    }
    return !failure;
}

/* Mette in *cosine e *sine il coseno e il seno di n u, con u l'angolo
 * dell'enunciato: nel punto u = pi, se trig_at_pi, altrimenti come frazioni
 * nella lettera t. Formula di De Moivre: n moltiplicazioni di
 * cos u + i sin u per se stesso; n negativo cambia segno al seno. */
static void trig_multiple(long long n, Rat *cosine, Rat *sine) {
    Rat t = rat_atom(trig_letter), square = rat_mul(t, t), one = rat_int(1);
    Rat c = trig_at_pi ? rat_int(-1) : rat_div(rat_add(one, square, 1), rat_add(one, square, 0));
    Rat s = trig_at_pi ? rat_int(0) : rat_div(rat_add(t, t, 0), rat_add(one, square, 0));
    *cosine = one;
    *sine = rat_int(0);
    for (long long i = 0; i < (n < 0 ? -n : n) && !failure; i++) {
        Rat real = rat_add(rat_mul(*cosine, c), rat_mul(*sine, s), 1);
        *sine = rat_add(rat_mul(*cosine, s), rat_mul(*sine, c), 0);
        *cosine = real;
    }
    if (n < 0) *sine = rat_add(rat_int(0), *sine, 1);
}

/* 18p-11. Vedi la dichiarazione prima di eval_call(). L'argomento del nodo
 * deve valere n u + b pi con n intero, dove u = g x è l'angolo
 * dell'enunciato. */
int trig_value(const Node *node, Rat argument, Rat *out) {
    Frac slope, turn;
    if (!trig_live || !trig_affine(argument, &slope, &turn)) return 0;
    Frac multiple = frac_div(slope, trig_scale);
    if (multiple.den != 1) return 0;

    Rat cn, sn, cb, sb;
    trig_multiple(multiple.num, &cn, &sn);
    if (!trig_constant(turn, &cb, &sb)) return 0;

    /* Formule di addizione. */
    Rat sine = rat_add(rat_mul(sn, cb), rat_mul(cn, sb), 0), cosine = rat_add(rat_mul(cn, cb), rat_mul(sn, sb), 1);
    *out = node->op == FN_SIN ? sine : node->op == FN_COS ? cosine : node->op == FN_TAN ? rat_div(sine, cosine) : rat_div(cosine, sine);
    return !failure;
}

/* =============================================================================
 * 18.10 L'ALBERO DEI SEGNI
 * ============================================================================
 *
 * Il segno di un confronto in un punto, calcolato dai segni dei polinomi
 * della tabella. La differenza dei due membri diventa un albero (SignNode):
 * foglie che sono frazioni di polinomi in una lettera, la variabile o quella
 * di uno spazio, e nodi per il prodotto, il quoziente e a + b sqrt(r). Lo
 * costruiscono sign_build() per le radici quadrate (18p-7), sign_ground()
 * per le lettere degli spazi (18p-8), sign_number_linear() per i confronti
 * con un numero come ln 6 (18p-10), powers_difference() per due monomi di
 * potenze (18p-9); sign_fraction() fa il conto e annota le condizioni di
 * esistenza, e sign_value() legge il segno in una riga.
 *
 * 18p-7. LE RADICI QUADRATE
 *
 * Un confronto può contenere radici quadrate, di numeri e di espressioni
 * nella variabile: x < 1 - \sqrt{2}, \sqrt{x + 3} = \sqrt{x + 12} - \sqrt{3 - x}.
 * La differenza dei due membri non è più una frazione di polinomi, ma il suo
 * segno si ricava ancora, in modo esatto, dai segni di polinomi.
 *
 * Ogni radice diventa una lettera s, con s^2 = R (il radicando) e s >= 0.
 * Un'espressione nelle lettere si scrive, raccogliendo le potenze pari di s,
 * come P + Q s, dove P e Q non contengono s. Dove R >= 0:
 *
 *   - se Q = 0, oppure R = 0, il segno è quello di P;
 *   - se P = 0, oppure P e Q hanno lo stesso segno, il segno è quello di Q;
 *   - se P e Q hanno segni opposti vince il più grande in valore assoluto
 *     tra P e Q s, cioè, confrontando i quadrati, il segno è quello di P
 *     moltiplicato per il segno di P^2 - Q^2 R.
 *
 * P, Q, R e P^2 - Q^2 R contengono una radice in meno: ripetendo si arriva a
 * frazioni di polinomi, le foglie, i cui segni sono le colonne della
 * tabella. Tra le colonne entrano così anche i polinomi P^2 - Q^2 R, ed è
 * giusto: le soluzioni di un'equazione con radici sono tra le radici del
 * polinomio che si ottiene elevando al quadrato, e la tabella, guardando i
 * segni di P e di Q, scarta da sola quelle che non lo sono.
 *
 * Un'espressione con radici ha un valore solo dove ogni radicando è
 * definito e non negativo: è una condizione di esistenza come un divisore
 * diverso da zero, e va posta per ogni radice anche se nei conti la lettera
 * è sparita, come in (\sqrt{x})^2.
 */

/* Il messaggio per un confronto che la tabella dei segni non tratta. */
static const char *const SIGN_SHAPE =
    "la tabella dei segni tratta solo espressioni razionali e radici quadrate nella variabile: niente logaritmi, funzioni goniometriche o altre lettere";

/* I tipi di nodo di un albero dei segni. */
typedef enum {
    SIGN_LEAF,   /* una frazione di polinomi in una lettera sola */
    SIGN_RATIO,  /* a / b */
    SIGN_TIMES,  /* a * b */
    SIGN_SURD    /* a + b sqrt(r) */
} SignKind;

/* Un nodo di un albero dei segni: un'espressione di cui si sa calcolare il
 * segno a partire dai segni dei polinomi di sign_poly[]. I nodi stanno in
 * sign_node[] e valgono per l'enunciato in corso. */
typedef struct SignNode SignNode;
struct SignNode {
    SignKind kind;
    int top, bottom, power, letter;  /* SIGN_LEAF: vale top / (bottom x^power),
                                        con top, bottom e letter posti in
                                        sign_poly[]; letter è il posto del
                                        polinomio x, o -1 se x non compare da
                                        sola a denominatore: così lo zero
                                        entra tra i punti solo quando serve */
    int space;                       /* SIGN_LEAF: -1 se la lettera x è la
                                        variabile dell'enunciato, altrimenti
                                        lo spazio di cui è la lettera (18p-8) */
    const SignNode *a, *b;           /* SIGN_RATIO, SIGN_TIMES e SIGN_SURD: gli operandi */
    const SignNode *r, *n;           /* SIGN_SURD: il radicando, e a^2 - b^2 r */
};

static SignNode sign_node[MAX_SIGN_NODES];
static int sign_nodes;

/* Una condizione di esistenza di un confronto: il nodo deve essere definito
 * e non negativo (strict = 0, un radicando), diverso da zero (strict = 1,
 * un divisore) oppure positivo (strict = 2, l'argomento di un logaritmo). */
typedef struct {
    const SignNode *node;
    int strict;
} SignNeed;

/* Le condizioni di esistenza dei confronti dell'enunciato in corso, a pezzi
 * consecutivi: ogni SignCase indica il suo. */
static SignNeed sign_need[MAX_SIGN_NEEDS];
static int sign_needs;

/* Un'espressione preparata per la tabella (18p-1): il suo albero dei segni e
 * le sue condizioni di esistenza, che sono `needs` voci di sign_need[] a
 * partire da first. */
typedef struct {
    const SignNode *value;
    int first, needs;
} SignCase;

/* Un confronto dell'enunciato, preparato per la tabella.
 *
 * Senza valori assoluti è un'espressione sola, la differenza dei due membri:
 * by_pattern[0]. Con k valori assoluti ce n'è una per ogni scelta dei segni
 * dei loro argomenti: nella scelta di numero p il valore assoluto i vale
 * l'argomento cambiato di segno se il bit i di p è 1. Quale scelta sia
 * quella vera in un punto lo dicono i segni degli argomenti:
 * inner[i][p] è l'argomento del valore assoluto i nella scelta p (conta solo
 * per i valori assoluti che stanno dentro il suo argomento, che hanno un
 * numero più basso). */
typedef struct {
    const Formula *source;  /* il confronto com'è nell'enunciato */
    int inner_count;        /* quanti valori assoluti, cioè le righe usate di inner[] */
    int identity;  /* 0 non ancora chiesto; 1 se i due membri sono la stessa
                      funzione, -1 se non risulta (formula_identity()) */
    int window;    /* 1 se il confronto è una finestra di un enunciato periodico
                      (18p-14): allora by_pattern[0] è il segno di u - gamma nel
                      giro numero home, e direction, 1 o -1, il segno per cui
                      moltiplicarlo per avere quello di left - right */
    int direction;
    long long home;
    SignCase inner[MAX_ABS][1 << MAX_ABS];
    SignCase by_pattern[1 << MAX_ABS];
} SignAtom;

/* I confronti dell'enunciato in corso, nell'ordine in cui sign_prepare() li
 * incontra; sign_compare() li ritrova dal nodo source. */
static SignAtom sign_atom[MAX_SIGN_ATOMS];
static int sign_atoms;

/* Mette in abs_node[] i valori assoluti dell'espressione node, quelli più
 * interni per primi, una volta ciascuno: due valori assoluti scritti allo
 * stesso modo, come il |u| di una funzione che ricompare nella sua derivata
 * (27f), hanno sempre lo stesso segno dell'argomento, e sono un valore
 * assoluto solo, con una sola scelta del segno (eval_call() li riconosce
 * allo stesso modo). */
void abs_collect(const Node *node) {
    if (!node || failure) return;
    abs_collect(node->a);
    abs_collect(node->b);
    abs_collect(node->c);
    if (node->kind != N_CALL || node->op != FN_ABS) return;
    for (int i = 0; i < abs_count; i++)
        if (abs_node[i] == node || node_equal(abs_node[i], node)) return;
    if (abs_count == MAX_ABS) { fail("troppi valori assoluti in un confronto"); return; }
    abs_node[abs_count++] = node;
}

/* Mette in surd_node[] le radici quadrate dell'espressione node, quelle più
 * interne per prime e una sola per radicando, e crea le loro lettere. */
static void surd_collect(const Node *node) {
    if (!node || failure) return;
    surd_collect(node->a);
    surd_collect(node->b);
    surd_collect(node->c);
    if (node->kind != N_CALL || node->op != FN_ROOT || node->b->kind != N_NUM || node->b->value != 2) return;
    for (int i = 0; i < surd_count; i++)
        if (node_equal(surd_node[i]->a, node->a)) return;
    if (surd_count == MAX_SURDS) { fail("troppe radici quadrate diverse in un confronto"); return; }
    surd_letter[surd_count] = atom_var(SURD_NAMES + surd_count);
    surd_node[surd_count++] = node;
}

/* Ritorna un nodo nuovo del tipo kind; se non c'è più posto annota un
 * errore e ritorna il primo, che non verrà usato. */
static SignNode *sign_node_new(SignKind kind) {
    if (sign_nodes == MAX_SIGN_NODES) { fail("espressione troppo complessa per la tabella dei segni"); return &sign_node[0]; }
    SignNode *node = &sign_node[sign_nodes++];
    memset(node, 0, sizeof *node);
    node->kind = kind;
    node->space = -1;
    return node;
}

/* Scrive il polinomio p come A + B s, dove s è la lettera della radice
 * numero i: mette A in *plain e B in *with, frazioni senza s. Una potenza
 * s^e con e = 2 j + r, r = 0 o 1, vale R^j s^r; con j negativo è una
 * divisione per R, lecita perché dove si divide per s il confronto chiede
 * già che s non sia zero. */
static void surd_split(Poly p, int i, Rat *plain, Rat *with) {
    *plain = *with = rat_int(0);
    for (int t = 0; t < p.count && !failure; t++) {
        Term term = p.term[t];
        Frac e = mono_exponent(&term.mono, surd_letter[i]);
        if (e.den != 1) { fail(SIGN_SHAPE); return; }
        long long half = frac_floor(frac_make(e.num, 2));
        term.mono = mono_with_exponent(&term.mono, surd_letter[i], frac_int(0));
        Rat piece = rat_mul((Rat){poly_term(term), poly_const(num_int(1))}, rat_pow_int(surd_inside[i], half));
        if (e.num - 2 * half) *with = rat_add(*with, piece, 0);
        else *plain = rat_add(*plain, piece, 0);
    }
}

/* Cerca tra le radici quelle che si ricavano dalle altre, e mette in
 * surd_value[] il loro valore: se il radicando R_j è q^2 R_a R_b, con q
 * razionale, allora sqrt(R_j) = q sqrt(R_a) sqrt(R_b). Vale anche con una
 * sola radice (R_j = q^2 R_a) e con nessuna (R_j = q^2, un quadrato).
 *
 * L'uguaglianza chiede che R_a e R_b non siano negativi, ma il confronto lo
 * chiede già, perché quelle radici vi compaiono: dove ha un valore,
 * l'uguaglianza vale. Serve a tenere bassa la torre: tre radici di cui una è
 * il prodotto delle altre due, come sqrt(4x + 5), sqrt(x - 1) e
 * sqrt(4x^2 + x - 5), sono due lettere e non tre, e i polinomi che ne
 * nascono hanno gradi e coefficienti molto più piccoli. */
static void surd_relate(void) {
    int derived[MAX_SURDS] = {0};
    for (int j = 0; j < surd_count && !failure; j++)
        for (int a = -1; a < surd_count && !derived[j]; a++)
            for (int b = a < 0 ? -1 : a + 1; b <= surd_count && !derived[j] && !failure; b++) {
                /* a e b scorrono sulle altre radici non ricavate; -1 per a,
                 * e surd_count per b, vogliono dire "nessuna". */
                int second = b < surd_count ? b : -1;
                if (a == j || second == j || (a >= 0 && derived[a]) || (second >= 0 && derived[second])) continue;
                if (a < 0 && second >= 0) continue;
                Rat product = rat_int(1);
                if (a >= 0) product = rat_mul(product, surd_inside[a]);
                if (second >= 0) product = rat_mul(product, surd_inside[second]);
                if (product.num.count == 0) continue;

                /* R_j deve essere c R_a R_b con c il quadrato di un razionale
                 * positivo. Si confrontano i prodotti in croce, che sono
                 * polinomi: se sono proporzionali il rapporto c è quello dei
                 * loro primi coefficienti, perché i termini sono in ordine. */
                Poly left = poly_mul(surd_inside[j].num, product.den), right = poly_mul(surd_inside[j].den, product.num);
                if (left.count == 0 || left.count != right.count || left.term[0].coef.im.num != 0 || right.term[0].coef.im.num != 0) continue;
                Frac ratio = frac_div(left.term[0].coef.re, right.term[0].coef.re);
                if (failure || ratio.num <= 0 || !poly_equal(left, poly_mul(right, poly_const(num_frac(ratio))))) continue;
                long long top = (long long)wide_isqrt(ratio.num), bottom = (long long)wide_isqrt(ratio.den);
                if (top * top != ratio.num || bottom * bottom != ratio.den) continue;
                surd_value[j] = rat_frac((Frac){top, bottom});
                if (a >= 0) surd_value[j] = rat_mul(surd_value[j], rat_atom(surd_letter[a]));
                if (second >= 0) surd_value[j] = rat_mul(surd_value[j], rat_atom(surd_letter[second]));
                derived[j] = 1;
            }
}

/* Prototipo in avanti inevitabile: sign_build() costruisce i suoi alberi con
 * sign_ground() e sign_surd(), che per i pezzi chiedono a loro volta un
 * albero a sign_build(), anche attraverso sign_constant(). */
static const SignNode *sign_build(Rat e, int level, int x);

/* Ritorna quale lettera di spazio compare nel polinomio p: -1 se nessuna,
 * il numero dello spazio se una sola, -2 se più d'una. */
static int poly_space(Poly p) {
    int found = -1;
    for (int t = 0; t < p.count; t++)
        for (int f = 0; f < p.term[t].mono.count; f++)
            for (int s = 0; s < spaces; s++) {
                if (p.term[t].mono.factor[f].atom != space[s].letter) continue;
                if (found >= 0 && found != s) return -2;
                found = s;
            }
    return found;
}

/* Ritorna 1 se l'atomo è un numero: il logaritmo di un primo, una potenza
 * di un primo con esponente razionale, il numero pi, o il numero e (la
 * lettera e, quando non è la variabile dell'enunciato). */
static int atom_is_number(int atom) {
    const Atom *a = &atoms[atom];
    if (a->kind == ATOM_VAR) return a->id == VAR_PI || (a->id == 'e' && sign_name != 'e');
    return (a->kind == ATOM_LN || a->kind == ATOM_POW) && a->base == BASE_PRIME && a->exponent.count == 0;
}

/* Ritorna 1 se p è un numero: tutti i suoi atomi lo sono. */
static int poly_is_number(Poly p) {
    for (int t = 0; t < p.count; t++)
        for (int f = 0; f < p.term[t].mono.count; f++)
            if (!atom_is_number(p.term[t].mono.factor[f].atom)) return 0;
    return 1;
}

/* Mette in *side il segno del numero p (vedi poly_is_number()) e ritorna 1;
 * annota un errore e ritorna 0 se non riesce a stabilirlo. Prima il conto
 * esatto, che riconosce lo zero; poi gli intervalli. */
static int number_side(Poly p, int *side) {
    Rat number = {p, poly_const(num_int(1))};
    if (number_sign(number, side) || range_side(poly_range(p), side)) { failure = NULL; return 1; }
    failure = NULL;
    fail("non riesco a stabilire il segno di una costante dell'enunciato");
    return 0;
}

/* Aggiunge a text, di size byte, i fattori del termine term il cui
 * esponente ha il segno di side (1: positivi, -1: negativi), scritti con
 * l'esponente in valore assoluto; ritorna quanti ne ha scritti. */
static int term_number_latex(const Term *term, int side, char *text, size_t size) {
    int written = 0;
    for (int f = 0; f < term->mono.count; f++) {
        const Atom *atom = &atoms[term->mono.factor[f].atom];
        Frac e = term->mono.factor[f].exp;
        char power[48] = "";
        if ((e.num > 0) != (side > 0)) continue;
        if (e.num < 0) e.num = -e.num;
        if (e.den != 1) snprintf(power, sizeof power, "^{\\frac{%lld}{%lld}}", e.num, e.den);
        else if (e.num != 1) snprintf(power, sizeof power, "^{%lld}", e.num);
        if (atom->kind == ATOM_VAR) text_add(text, size, "%s%s", atom->id == VAR_PI ? "\\pi" : "e", power);
        else if (atom->kind == ATOM_LN) text_add(text, size, "%s\\ln%s %lld", written ? " " : "", power, atom->id);
        else if (e.num == 1 && e.den == 2) text_add(text, size, "\\sqrt{%lld}", atom->id);
        else text_add(text, size, " %lld%s", atom->id, power);
        written++;
    }
    return written;
}

/* Aggiunge a text, di size byte, il numero p in LaTeX (vedi
 * poly_is_number()): una somma di termini, ognuno un razionale per un
 * prodotto di \ln p, di potenze di primi e di potenze di e, con i fattori
 * di esponente negativo a denominatore. Ciò che scrive si rilegge, con il
 * parser, come lo stesso numero. */
static void poly_number_latex(Poly p, char *text, size_t size) {
    if (p.count == 0) text_add(text, size, "0");
    for (int t = 0; t < p.count; t++) {
        const Term *term = &p.term[t];
        Frac c = term->coef.re;
        long long top = c.num < 0 ? -c.num : c.num;
        int above = 0, below = c.den != 1;
        for (int f = 0; f < term->mono.count; f++)
            if (term->mono.factor[f].exp.num > 0) above = 1; else below = 1;
        text_add(text, size, "%s", t == 0 ? (c.num < 0 ? "-" : "") : (c.num < 0 ? " - " : " + "));
        if (below) text_add(text, size, "\\frac{");
        if (top != 1 || !above) text_add(text, size, "%lld", top);
        term_number_latex(term, 1, text, size);
        if (!below) continue;
        text_add(text, size, "}{");
        if (c.den != 1) text_add(text, size, "%lld", c.den);
        term_number_latex(term, -1, text, size);
        text_add(text, size, "}");
    }
}

/* Aggiunge a text, di size byte, il numero r in LaTeX: il numeratore, o una
 * frazione se il denominatore non è 1. */
static void number_latex(Rat r, char *text, size_t size) {
    if (poly_is_one(r.den)) { poly_number_latex(r.num, text, size); return; }
    text_add(text, size, "\\frac{");
    poly_number_latex(r.num, text, size);
    text_add(text, size, "}{");
    poly_number_latex(r.den, text, size);
    text_add(text, size, "}");
}

/* Ritorna l'albero dei segni della costante di segno side (-1, 0 o 1). */
static const SignNode *sign_constant(int side, int x) { return sign_build(rat_int(side), 0, x); }

/* Ritorna l'albero dei segni del prodotto di a e b. */
static const SignNode *sign_times(const SignNode *a, const SignNode *b) {
    SignNode *node = sign_node_new(SIGN_TIMES);
    node->a = a;
    node->b = b;
    return node;
}

/* 18p-10. Se p = A x + B, con A e B numeri (vedi poly_is_number()) e non
 * tutti e due razionali, mette in *out l'albero dei segni di p e ritorna 1.
 *
 * È il caso di un confronto della variabile con una costante che contiene
 * logaritmi o il numero e: x < \ln 6, x \neq \frac{\ln 3}{\ln 5}. Se A è zero
 * p è una costante, e ha il suo segno. Altrimenti p si annulla in
 * k = -B / A e ha il segno di A per quello di x - k. Se k risulta razionale
 * (ln 8 / ln 2 = 3, che il conto esatto semplifica) è un punto qualsiasi
 * della tabella; se no è un numero che non è radice di un polinomio, e
 * prende un posto suo (Kappa). */
static int sign_number_linear(Poly p, int x, const SignNode **out) {
    Poly part[2], one = poly_const(num_int(1));
    Num plain;
    int side = 0, degree = poly_split(p, x, part, 1);
    if (degree < 0 || !poly_is_number(part[0]) || (degree == 1 && !poly_is_number(part[1]))) return 0;
    if (degree == 0) {
        if (number_side(part[0], &side)) *out = sign_constant(side, x);
        return 1;
    }
    if (!number_side(part[1], &side)) return 1;
    Rat root = rat_div(rat_add(rat_int(0), (Rat){part[0], one}, 1), (Rat){part[1], one});
    if (failure) return 1;

    /* Il conto esatto semplifica i monomi, non i polinomi: (2 ln 2 - ln 3) /
     * (2 ln 3 - 4 ln 2) resta scritto così, ed è -1/2. Lo si riconosce
     * perché numeratore e denominatore sono proporzionali. E si scrive la
     * frazione con il primo coefficiente del denominatore positivo. */
    if (root.num.count == 0)
        root = rat_int(0);
    else if (poly_proportional(root.num, root.den) && root.num.term[0].coef.im.num == 0 && root.den.term[0].coef.im.num == 0)
        root = rat_frac(frac_div(root.num.term[0].coef.re, root.den.term[0].coef.re));
    else if (root.den.count > 0 && root.den.term[0].coef.re.num < 0)
        root = (Rat){poly_add(poly_const(num_int(0)), root.num, 1), poly_add(poly_const(num_int(0)), root.den, 1)};
    if (rat_number(root, &plain) && plain.im.num == 0) {
        *out = sign_times(sign_constant(side, x), sign_build(rat_add(rat_atom(x), rat_frac(plain.re), 1), 0, x));
        return 1;
    }
    char text[96] = "";
    number_latex(root, text, sizeof text);
    SignNode *leaf = sign_node_new(SIGN_LEAF);
    leaf->top = sign_column_kappa(range_div(range_neg(poly_range(part[0])), poly_range(part[1])), text, &root);
    leaf->bottom = sign_column((Uni){0, {1}});
    leaf->letter = -1;
    *out = sign_times(sign_constant(side, x), leaf);
    return 1;
}

/* 18p-8. Se p è una somma di logaritmi nella stessa base b, con
 * coefficienti razionali, più una costante,
 *
 *     K (w_1 log_b f_1 + ... + w_k log_b f_k + c),
 *
 * mette in *out un albero dei segni con lo stesso segno e ritorna 1. La
 * costante c può essere un razionale, oppure contenere logaritmi di numeri:
 * serve solo che c ln b sia una somma u_2 ln 2 + u_3 ln 3 + ..., cioè il
 * logaritmo naturale del razionale q = 2^(u_2) 3^(u_3) ... Allora, con D un
 * intero positivo che rende interi tutti gli esponenti,
 *
 *     segno della somma = segno di  q^D f_1^(D w_1) ... f_k^(D w_k) - 1,
 *
 * perché moltiplicare per D non cambia il segno, la somma dei logaritmi è
 * il logaritmo del prodotto, e un logaritmo in base b > 1 è positivo
 * esattamente quando l'argomento supera 1. Vale dove gli f_i sono positivi,
 * cioè dove il confronto ha un valore. Il fattore K davanti, un numero,
 * porta il suo segno.
 *
 * Ritorna 0, senza fare nulla, se p non ha questa forma. */
static int sign_log_linear(Poly p, int x, const SignNode **out) {
    Poly part[MAX_SPACES], rest = poly_const(num_int(0)), one = poly_const(num_int(1));
    Frac weight[MAX_SPACES];
    int first = -1, side = 1;
    for (int s = 0; s < spaces; s++) part[s] = rest;

    /* I coefficienti dei logaritmi, e ciò che non ne contiene. */
    for (int t = 0; t < p.count; t++) {
        Term bare = p.term[t];
        int where = -1;
        for (int f = 0; f < p.term[t].mono.count; f++) {
            int atom = p.term[t].mono.factor[f].atom, s = space_of(atom);
            if (s == spaces && atom_is_number(atom)) continue;
            if (s == spaces || space[s].kind != SPACE_LOG || where >= 0 || frac_cmp(p.term[t].mono.factor[f].exp, frac_int(1)) != 0) return 0;
            where = s;
            bare.mono = mono_with_exponent(&bare.mono, atom, frac_int(0));
        }
        if (where < 0) { rest = poly_add(rest, poly_term(bare), 0); continue; }
        if (first >= 0 && (space[where].natural != space[first].natural || (!space[where].natural && frac_cmp(space[where].base, space[first].base) != 0))) return 0;
        if (first < 0) first = where;
        part[where] = poly_add(part[where], poly_term(bare), 0);
    }
    if (first < 0) return 0;

    /* I pesi: ogni coefficiente è un multiplo razionale del primo. */
    long long common = 1;
    for (int s = 0; s < spaces; s++) {
        weight[s] = frac_int(s == first);
        if (s == first || part[s].count == 0) continue;
        if (!poly_proportional(part[s], part[first]) || part[s].term[0].coef.im.num != 0 || part[first].term[0].coef.im.num != 0) return 0;
        weight[s] = frac_div(part[s].term[0].coef.re, part[first].term[0].coef.re);
        common = lcm_small(common, weight[s].den);
    }

    /* c ln b = (rest / K) ln b, come somma di logaritmi di primi. Se K è
     * un razionale, rest deve esserlo; se K è un multiplo di ln b (capita
     * quando il confronto contiene il logaritmo di un numero, che porta
     * ln b a denominatore), rest / K per ln b è rest diviso quel multiplo. */
    Poly base_log = space[first].natural ? one : logarithm_of_positive(rat_frac(space[first].base)).num, sum;
    Frac ratio;
    if (failure) return 0;
    if (part[first].count == 1 && part[first].term[0].mono.count == 0) {
        ratio = part[first].term[0].coef.re;
        sum = poly_mul(rest, base_log);
    } else if (!space[first].natural && poly_proportional(part[first], base_log)) {
        ratio = frac_div(part[first].term[0].coef.re, base_log.term[0].coef.re);
        sum = rest;
    } else {
        return 0;
    }
    if (failure || !number_side(part[first], &side)) return 0;

    /* I primi e i loro esponenti u_p = coefficiente / K; poi il prodotto. */
    for (int pass = 0; pass < 2; pass++) {
        Rat product = rat_int(1);
        for (int t = 0; t < sum.count; t++) {
            const Term *term = &sum.term[t];
            const Atom *atom = term->mono.count == 1 ? &atoms[term->mono.factor[0].atom] : NULL;
            if (!atom || atom->kind != ATOM_LN || atom->base != BASE_PRIME || frac_cmp(term->mono.factor[0].exp, frac_int(1)) != 0 || term->coef.im.num != 0) return 0;
            Frac power = frac_div(term->coef.re, ratio);
            if (pass == 0) common = lcm_small(common, power.den);
            else product = rat_mul(product, rat_pow_int(rat_int(atom->id), power.num * (common / power.den)));
        }
        if (pass == 0) continue;
        for (int s = 0; s < spaces && !failure; s++)
            if (weight[s].num != 0) product = rat_mul(product, rat_pow_int(eval(space[s].argument), weight[s].num * (common / weight[s].den)));
        *out = sign_times(sign_constant(side, x), sign_build(rat_add(product, rat_int(1), 1), surd_count, x));
    }
    return 1;
}

/* Prototipo in avanti inevitabile: sign_ground() passa a sign_one_ratio() i
 * polinomi in un rapporto di esponenziali, e sign_one_ratio() le ridà i
 * fattori di due termini. */
static const SignNode *sign_ground(Poly p, int x);

/* 18p-8, regola e di sign_ground(). Se i termini di p sono tutti un numero
 * razionale per un prodotto di potenze di lettere di esponenziali, e quei
 * prodotti sono tutti potenze di uno stesso monomio m per un monomio comune,
 * mette in *out l'albero dei segni di p e ritorna 1; ritorna 0 se p non ha
 * questa forma, o se non la si sa trattare.
 *
 * È l'equazione "omogenea" dei libri: in 2 \cdot 4^x - 5 \cdot 6^x + 3 \cdot 9^x,
 * con le lettere a = 2^x e b = 3^x, i termini sono 2a^2, -5ab, 3b^2, cioè
 * b^2 per un polinomio in m = a / b: 2m^2 - 5m + 3. In generale
 * p = M Q(m), con M un monomio, che è positivo, e Q un polinomio in una
 * variabile; m è un esponenziale, positivo anche lui. Q si scompone: per
 * ogni radice razionale positiva r/s il fattore s m - r, il cui segno è
 * quello di s M+ - r M- (m = M+ / M-), un polinomio di due termini che
 * tratta la regola d; un fattore con la radice negativa o nulla è positivo;
 * ciò che resta, se non ha radici positive (lo dice il teorema di Sturm), ha
 * sugli m positivi il segno che ha in m = 1. Se resta una radice positiva
 * irrazionale il confronto non è trattato: servirebbe il logaritmo di un
 * numero che non è razionale. */
static int sign_one_ratio(Poly p, int x, const SignNode **out) {
    long long exponent[MAX_UNIVARIATE + 1][MAX_SPACES], step[MAX_SPACES], power[MAX_UNIVARIATE + 1], c[MAX_UNIVARIATE + 1] = {0};
    long long common = 0, scale = 1, lowest = 0, highest = 0;
    Frac root[MAX_UNIVARIATE + 2];
    if (p.count < 2 || p.count > MAX_UNIVARIATE + 1) return 0;

    /* Gli esponenti delle lettere in ogni termine. */
    for (int t = 0; t < p.count; t++) {
        const Term *term = &p.term[t];
        if (term->coef.im.num != 0) return 0;
        for (int i = 0; i < spaces; i++) exponent[t][i] = 0;
        for (int f = 0; f < term->mono.count; f++) {
            int i = space_of(term->mono.factor[f].atom);
            if (i == spaces || space[i].kind != SPACE_EXP || term->mono.factor[f].exp.den != 1) return 0;
            exponent[t][i] = term->mono.factor[f].exp.num;
        }
        scale = lcm_small(scale, term->coef.re.den);
        if (scale > 1000000) return 0;
    }

    /* Il monomio m: la differenza tra due termini, ridotta ai minimi termini
     * e con il primo esponente positivo. */
    for (int i = 0; i < spaces; i++) common = (long long)gcd128(common, exponent[1][i] - exponent[0][i]);
    if (common == 0) return 0;
    for (int i = 0, seen = 0; i < spaces; i++) {
        step[i] = (exponent[1][i] - exponent[0][i]) / common;
        if (!seen && step[i] < 0) common = -common, step[i] = -step[i];
        seen |= step[i] != 0;
    }

    /* Ogni termine è il primo per una potenza intera di m. */
    for (int t = 0; t < p.count; t++) {
        int lead = 0;
        while (step[lead] == 0) lead++;
        power[t] = (exponent[t][lead] - exponent[0][lead]) / step[lead];
        for (int i = 0; i < spaces; i++)
            if (exponent[t][i] - exponent[0][i] != power[t] * step[i]) return 0;
        if (power[t] < lowest) lowest = power[t];
        if (power[t] > highest) highest = power[t];
    }
    int degree = (int)(highest - lowest);
    if (highest - lowest > MAX_UNIVARIATE) return 0;
    for (int t = 0; t < p.count; t++) {
        Frac value = frac_mul(p.term[t].coef.re, frac_int(scale));
        if (failure || value.num > LLONG_MAX / 4 || value.num < -(LLONG_MAX / 4)) return 0;
        c[power[t] - lowest] = value.num;
    }

    /* Q e le sue radici razionali; M+ e M-. */
    Uni rest = {degree, {0}}, quotient;
    Mono plus = {0}, minus = {0};
    const SignNode *tree = NULL;
    int roots = rational_roots(c, degree, root);
    if (roots < 0) return 0;
    for (int i = 0; i <= degree; i++) rest.c[i] = c[i];
    for (int i = 0; i < spaces; i++) {
        if (step[i] > 0) plus = mono_with_exponent(&plus, space[i].letter, frac_int(step[i]));
        if (step[i] < 0) minus = mono_with_exponent(&minus, space[i].letter, frac_int(-step[i]));
    }
    for (int r = 0; r < roots && !failure; r++) {
        Uni linear = {1, {-(__int128)root[r].num, root[r].den}};
        const SignNode *factor = root[r].num > 0 ? sign_ground(poly_add(poly_term((Term){num_int(root[r].den), plus}), poly_term((Term){num_int(root[r].num), minus}), 1), x) : NULL;

        /* Una radice multipla dà lo stesso fattore più volte. */
        while (!failure && uni_divide(&rest, &linear, &quotient)) {
            rest = quotient;
            if (factor) tree = tree ? sign_times(tree, factor) : factor;
        }
    }
    if (failure) return 0;

    /* Ciò che resta non deve annullarsi per m positivo. */
    if (rest.degree >= 1) {
        Wide bound = uni_bound(&rest);
        sturm_build(&rest);
        if (failure || sturm_changes((Wide){0, 1}) - sturm_changes(bound) != 0) return 0;
    }
    const SignNode *sign = sign_constant(uni_sign_at(&rest, (Wide){1, 1}), x);
    *out = tree ? sign_times(sign, tree) : sign;
    return !failure;
}

/* 18p-8. Ritorna l'albero dei segni del polinomio p, che non contiene
 * radici ma può contenere la variabile (atomo x), lettere di spazi e numeri
 * come ln 2.
 *
 *   a. Una somma di logaritmi: sign_log_linear().
 *   b. Una lettera sola, la variabile o quella di uno spazio, con
 *      coefficienti razionali: una foglia. Con la variabile e coefficienti
 *      che sono numeri non razionali: sign_number_linear().
 *   c. Più lettere. Una lettera di spazio che divide tutti i termini si
 *      raccoglie. Poi si sceglie una lettera g e si scrive p come polinomio
 *      in g, con i coefficienti nelle altre lettere: se sono tutti multipli
 *      razionali di uno stesso polinomio U, allora p = U V(g), e il segno è
 *      il prodotto dei due segni.
 *   d. Due termini soli, ognuno un numero per un prodotto di potenze di
 *      esponenziali: c_1 M_1 + c_2 M_2. Se c_1 e c_2 hanno lo stesso segno
 *      è il loro. Altrimenti il segno è quello del logaritmo del rapporto
 *      |c_1| M_1 / (|c_2| M_2), che è A x + B con A e B numeri fatti di
 *      logaritmi: di nuovo sign_number_linear(). È così che si risolve
 *      2^x = 3^(x+1).
 *   e. Più di due termini, tutti potenze di uno stesso monomio di
 *      esponenziali per un monomio comune: un polinomio in quel monomio
 *      (sign_one_ratio()).
 *
 * In ogni altro caso le lettere sono davvero mescolate, e il confronto non
 * è trattato. */
static const SignNode *sign_ground(Poly p, int x) {
    const SignNode *found = &sign_node[0];
    int s = poly_space(p);
    if (failure) return found;
    if (s != -1 && sign_log_linear(p, x, &found)) return found;

    /* b. */
    if (s == -1 || (s >= 0 && !poly_uses(p, x))) {
        Uni top;
        int up;
        if (!uni_from_poly(p, s < 0 ? x : space[s].letter, &top, &up)) {
            if (failure || s != -1 || !sign_number_linear(p, x, &found)) fail(SIGN_SHAPE);
            return found;
        }
        SignNode *leaf = sign_node_new(SIGN_LEAF);
        leaf->space = s;
        leaf->top = sign_column_in(top, s);
        leaf->bottom = sign_column_in((Uni){0, {1}}, s);
        leaf->power = up;
        leaf->letter = up ? sign_column_in((Uni){1, {0, 1}}, s) : -1;
        return leaf;
    }

    /* c. La lettera g: quella dell'ultimo spazio che compare. lowest è il
     * suo esponente più basso tra tutti i termini. */
    int g = spaces - 1;
    while (g > 0 && !poly_uses(p, space[g].letter)) g--;

    /* Una lettera che divide tutti i termini si raccoglie, qualunque sia:
     * L_1^2 - L_1 L_2 è L_1 (L_1 - L_2) anche se la lettera scelta è L_2. */
    for (int h = g; h >= 0; h--) {
        long long lowest = LLONG_MAX;
        for (int t = 0; t < p.count; t++) {
            Frac e = mono_exponent(&p.term[t].mono, space[h].letter);
            if (e.den != 1) { fail(SIGN_SHAPE); return found; }
            if (e.num < lowest) lowest = e.num;
        }
        if (lowest == 0) continue;

        /* p = h^lowest per un polinomio senza h a fattor comune. Con lowest
         * negativo h sta a denominatore, e il segno di h^lowest è quello di
         * h^(-lowest): dove h è zero il confronto non ha un valore. */
        Poly factor = poly_term((Term){num_int(1), mono_atom(space[h].letter, frac_int(lowest < 0 ? -lowest : lowest))});
        return sign_times(sign_ground(factor, x), sign_ground(poly_mul(p, poly_term((Term){num_int(1), mono_atom(space[h].letter, frac_int(-lowest))})), x));
    }
    Poly part[MAX_UNI + 1];
    int degree = poly_split(p, space[g].letter, part, MAX_UNI), lead = 0, apart = degree >= 0;
    while (apart && part[lead].count == 0) lead++;

    /* I coefficienti devono essere multipli di part[lead]: i rapporti sono
     * i coefficienti di V. */
    Poly other = poly_const(num_int(0));
    for (int j = lead; j <= degree && apart; j++) {
        if (part[j].count == 0) continue;
        if (!poly_proportional(part[j], part[lead])) { apart = 0; break; }
        Num ratio = num_mul(part[j].term[0].coef, num_inv(part[lead].term[0].coef));
        other = poly_add(other, poly_term((Term){ratio, j ? mono_atom(space[g].letter, frac_int(j)) : (Mono){0}}), 0);
    }
    if (apart) return sign_times(sign_ground(part[lead], x), sign_ground(other, x));

    /* e. Più di due termini: potenze di uno stesso monomio di
     * esponenziali (sign_one_ratio()). */
    if (p.count > 2) {
        if (!sign_one_ratio(p, x, &found) && !failure) fail(SIGN_SHAPE);
        return found;
    }

    /* d. Il logaritmo del rapporto dei due termini: per ogni lettera
     * p^(x/L) con esponente k nel rapporto, (k / L) x ln p (ln e = 1). */
    if (p.count != 2 || p.term[0].coef.im.num != 0 || p.term[1].coef.im.num != 0) { fail(SIGN_SHAPE); return found; }

    /* I due termini devono essere fatti solo di lettere di esponenziali,
     * che sono positive: lo si controlla prima di ogni altra cosa. Una
     * versione che guardava i segni dei coefficienti senza questo controllo
     * dava per positivo x + 2^x, cioè risolveva x + 2^x > 0 con "ogni x". */
    for (int side = 0; side < 2; side++)
        for (int f = 0; f < p.term[side].mono.count; f++) {
            int space_number = space_of(p.term[side].mono.factor[f].atom);
            if (space_number == spaces || space[space_number].kind != SPACE_EXP || p.term[side].mono.factor[f].exp.den != 1) { fail(SIGN_SHAPE); return found; }
        }
    Frac first = p.term[0].coef.re, second = p.term[1].coef.re;
    if ((first.num > 0) == (second.num > 0)) return sign_constant(first.num > 0 ? 1 : -1, x);
    Rat log_ratio = logarithm_of_positive(rat_frac(frac_div(first.num < 0 ? frac_neg(first) : first, second.num < 0 ? frac_neg(second) : second)));
    for (int side = 0; side < 2 && !failure; side++)
        for (int f = 0; f < p.term[side].mono.count && !failure; f++) {
            Frac e = p.term[side].mono.factor[f].exp;
            const Space *sp = &space[space_of(p.term[side].mono.factor[f].atom)];
            Rat slope = rat_mul(rat_frac(frac_make(side ? -e.num : e.num, sp->scale)), sp->prime ? logarithm_of_positive(rat_int(sp->prime)) : rat_int(1));
            log_ratio = rat_add(log_ratio, rat_mul(slope, rat_atom(x)), 0);
        }
    if (failure) return found;

    /* p ha il segno del suo primo coefficiente dove il rapporto supera 1. */
    SignNode *ratio = sign_node_new(SIGN_RATIO);
    ratio->a = sign_ground(log_ratio.num, x);
    ratio->b = sign_ground(log_ratio.den, x);
    return sign_times(sign_constant(first.num > 0 ? 1 : -1, x), ratio);
}

/* Ritorna l'albero dei segni di a + b s, dove s è la radice numero i e a e
 * b contengono solo le radici precedenti. */
static const SignNode *sign_surd(Rat a, Rat b, int i, int x) {
    if (b.num.count == 0) return sign_build(a, i, x);
    SignNode *node = sign_node_new(SIGN_SURD);
    Rat norm = rat_add(rat_mul(a, a), rat_mul(rat_mul(b, b), surd_inside[i]), 1);
    node->a = sign_build(a, i, x);
    node->b = sign_build(b, i, x);
    node->r = sign_build(surd_inside[i], i, x);
    node->n = sign_build(norm, i, x);
    return node;
}

/* 18p-7. Ritorna l'albero dei segni della frazione e, che può contenere la
 * variabile di atomo x e le lettere delle prime `level` radici. Annota un
 * errore se contiene altro. */
static const SignNode *sign_build(Rat e, int level, int x) {
    if (failure) return &sign_node[0];

    /* Le radici che non compaiono non contano; senza radici e senza lettere
     * di spazi è una foglia, con numeratore e denominatore tra le colonne
     * della tabella e le potenze di x a denominatore tenute a parte. Con le
     * lettere degli spazi, numeratore e denominatore vanno ognuno per conto
     * suo (18p-8). */
    while (level > 0 && !poly_uses(e.num, surd_letter[level - 1]) && !poly_uses(e.den, surd_letter[level - 1])) level--;
    Uni top, bottom;
    int up, down;
    if (level == 0 && (poly_space(e.num) != -1 || poly_space(e.den) != -1 || !uni_from_poly(e.num, x, &top, &up) || !uni_from_poly(e.den, x, &bottom, &down))) {
        SignNode *node = sign_node_new(SIGN_RATIO);
        node->a = sign_ground(e.num, x);
        node->b = sign_ground(e.den, x);
        return node;
    }
    if (level == 0) {
        SignNode *leaf = sign_node_new(SIGN_LEAF);
        leaf->top = sign_column(top);
        leaf->bottom = sign_column(bottom);
        leaf->power = up - down;
        leaf->letter = up || down ? sign_column((Uni){1, {0, 1}}) : -1;
        return leaf;
    }

    /* Numeratore e denominatore, ognuno come P + Q s nell'ultima radice. */
    Rat a, b, c, d;
    surd_split(e.num, level - 1, &a, &b);
    surd_split(e.den, level - 1, &c, &d);
    if (failure) return &sign_node[0];
    SignNode *node = sign_node_new(SIGN_RATIO);
    node->a = sign_surd(a, b, level - 1, x);
    node->b = sign_surd(c, d, level - 1, x);
    return node;
}

/* Prototipo in avanti inevitabile: il tratto in cui sta la lettera di uno
 * spazio (space_row()) si legge dai confronti dei suoi gradini, cioè da
 * sign_compare(), che a sua volta legge i segni delle foglie negli spazi
 * attraverso space_row(). sign_compare() sta nel capitolo 18.11, con i
 * confronti preparati. */
int sign_compare(const Formula *f, const int *sign, int *defined);

/* Ritorna in quale tratto del suo spazio sta la lettera dello spazio s,
 * nella riga della tabella in cui i polinomi hanno i segni di sign[]: con k
 * gradini sotto di sé sta nel tratto 2k, e se è proprio su un gradino, che
 * allora è il gradino numero k, nel tratto 2k + 1. I gradini sono in ordine
 * crescente, quindi quelli sotto sono i primi. */
static int space_row(int s, const int *sign, int *defined) {
    int below = 0, on = 0;
    for (int j = 0; j < space[s].steps; j++) {
        const Step *step = &space[s].step[j];
        int side = step->above ? sign_compare(step->above, sign, defined) : sign[step->kappa];
        if (side > 0) below++;
        else if (side == 0) on = 1;
    }
    return 2 * below + on;
}

/* Ritorna il segno del polinomio della colonna column, che è nella lettera
 * dello spazio s, quando la lettera sta nel tratto row (vedi space_row()).
 * Su un gradino è zero se il polinomio del gradino lo divide (18p-5); in un
 * tratto aperto lo si calcola in un razionale del tratto. Per un
 * esponenziale il primo tratto va da zero, escluso, al primo gradino. */
static int space_sign(int s, int row, int column) {
    const Space *sp = &space[s];
    const Uni *p = &sign_poly[column];
    int k = row / 2;
    Uni rest;
    if (row % 2) {
        const Step *step = &sp->step[k];
        if (step->exact) return uni_sign_at(p, step->low);
        return uni_divide(p, &step->element, &rest) ? 0 : uni_sign_at(p, wide_mid(step->low, step->high));
    }
    if (sp->steps == 0) return uni_sign_at(p, (Wide){1, 1});
    if (k == sp->steps) return uni_sign_at(p, (Wide){sp->step[k - 1].high.num / sp->step[k - 1].high.den + 2, 1});
    if (k > 0) return uni_sign_at(p, wide_between(sp->step[k - 1].high, sp->step[k].low));
    return uni_sign_at(p, sp->kind == SPACE_EXP ? wide_between((Wide){0, 1}, sp->step[0].low) : (Wide){sp->step[0].low.num / sp->step[0].low.den - 2, 1});
}

/* Ritorna il segno del nodo dove i polinomi hanno i segni di sign[]; mette 0
 * in *defined, che chi chiama ha messo a 1, se lì non ha valore. Le regole
 * per SIGN_SURD sono quelle in testa a 18p-7. */
static int sign_value(const SignNode *node, const int *sign, int *defined) {
    if (node->kind == SIGN_LEAF && node->space < 0) {
        if (sign[node->bottom] == 0 || (node->letter >= 0 && sign[node->letter] == 0)) *defined = 0;
        return sign[node->top] * sign[node->bottom] * (node->power % 2 ? sign[node->letter] : 1);
    }
    if (node->kind == SIGN_LEAF) {
        /* Una foglia in uno spazio: gli stessi tre segni, letti nel tratto
         * in cui sta la lettera. */
        int row = space_row(node->space, sign, defined);
        int below = space_sign(node->space, row, node->bottom), letter = node->letter >= 0 ? space_sign(node->space, row, node->letter) : 1;
        if (below == 0 || letter == 0) *defined = 0;
        return space_sign(node->space, row, node->top) * below * (node->power % 2 ? letter : 1);
    }
    int plain = sign_value(node->a, sign, defined), with = sign_value(node->b, sign, defined);
    if (node->kind == SIGN_TIMES) return plain * with;
    if (node->kind == SIGN_RATIO) {
        if (with == 0) *defined = 0;
        return plain * with;
    }
    int inside = sign_value(node->r, sign, defined), norm = sign_value(node->n, sign, defined);
    if (inside < 0) *defined = 0;
    if (with == 0 || inside == 0) return plain;
    if (plain == 0 || plain == with) return with;
    return plain * norm;
}

/* Aggiunge alle condizioni di esistenza di *out che la frazione e sia non
 * negativa (strict = 0), diversa da zero (1) o positiva (2). */
static void sign_require(SignCase *out, Rat e, int level, int strict, int x) {
    if (failure) return;
    if (sign_needs == MAX_SIGN_NEEDS) { fail("troppe condizioni di esistenza in un enunciato"); return; }
    sign_need[sign_needs++] = (SignNeed){sign_build(e, level, x), strict};
    out->needs++;
}

/* 18p-9. MONOMI DI POTENZE
 *
 * 2^(x+5) 3^(x+2) <= 8 * 6^((3x-1)/x) ha la variabile in esponenti che non
 * sono di primo grado, e le lettere di 18p-8 non bastano. Ma i due membri
 * sono monomi: prodotti di potenze di numeri positivi. Un monomio così è
 *
 *     prodotto sui primi p di p^(H_p(x)),      con gli H_p frazioni in x,
 *
 * e il segno della differenza di due monomi positivi è il segno della
 * differenza dei loro logaritmi, cioè di una somma di H_p(x) ln p. Se gli
 * H_p sono tutti multipli razionali di uno stesso H, H_p = w_p H, la somma è
 * H(x) ln W con W = prodotto dei p^(w_p), un razionale: il segno è quello
 * di H(x) se W > 1, il suo opposto se W < 1. Resta un confronto tra frazioni
 * in x. Nell'esempio, portato tutto a sinistra, H_2 = H_3 = x - 1 + 1/x.
 *
 * Se gli H_p non sono proporzionali, come in 2^x = 3^(x+1), il confronto
 * non è di questo tipo.
 */

/* Un monomio di potenze in costruzione: per ogni primo l'esponente, una
 * frazione nella variabile. */
typedef struct {
    int count;                     /* quanti primi, in prime[] */
    long long prime[MAX_FACTORS];  /* i primi, ognuno una volta */
    Rat power[MAX_FACTORS];        /* l'esponente di prime[i], una frazione in x */
} Powers;

/* Moltiplica il monomio *m per prime elevato a power. Ritorna 0 se i primi
 * sono troppi. */
static int powers_times(Powers *m, long long prime, Rat power) {
    int i = 0;
    while (i < m->count && m->prime[i] != prime) i++;
    if (i == MAX_FACTORS) return 0;
    if (i == m->count) { m->prime[m->count++] = prime; m->power[i] = rat_int(0); }
    m->power[i] = rat_add(m->power[i], power, 0);
    return 1;
}

/* Moltiplica *m per il monomio dell'espressione node elevato a scale, e
 * ritorna 1; ritorna 0 se node non è un monomio di potenze: un numero
 * positivo, un prodotto, un quoziente, una potenza o una radice di monomi.
 * Gli esponenti e gli indici delle radici sono espressioni qualsiasi. */
static int powers_read(const Node *node, Rat scale, Powers *m) {
    long long prime, times;
    if (failure) return 0;
    switch (node->kind) {
    case N_NUM: {
        long long value = node->value;
        if (value <= 0) return 0;
        while (pop_prime(&value, &prime, &times))
            if (!powers_times(m, prime, rat_mul(scale, rat_int(times)))) return 0;
        return 1;
    }
    case N_MUL: return powers_read(node->a, scale, m) && powers_read(node->b, scale, m);
    case N_DIV: return powers_read(node->a, scale, m) && powers_read(node->b, rat_add(rat_int(0), scale, 1), m);
    case N_POW: return powers_read(node->a, rat_mul(scale, eval(node->b)), m);
    case N_CALL:
        if (node->op != FN_ROOT) return 0;
        return powers_read(node->a, rat_div(scale, eval(node->b)), m);
    default: return 0;
    }
}

/* 18p-9. Se left e right sono monomi di potenze con la variabile in qualche
 * esponente, e gli esponenti dei primi nel loro rapporto sono proporzionali,
 * mette in *out una frazione nella variabile che ha il segno di
 * left - right e ritorna 1. Le condizioni di esistenza degli esponenti
 * restano annotate in conditions[]. Altrimenti ritorna 0. */
static int powers_difference(const Node *left, const Node *right, Rat *out) {
    Powers m = {0};
    int lead = -1;
    Frac weight[MAX_FACTORS];
    if (!node_uses_letter(left, sign_name) && !node_uses_letter(right, sign_name)) return 0;

    /* "A - B confrontato con 0" è "A confrontato con B". */
    if (left->kind == N_SUB && right->kind == N_NUM && right->value == 0) {
        right = left->b;
        left = left->a;
    }
    if (!powers_read(left, rat_int(1), &m) || !powers_read(right, rat_int(-1), &m) || failure) return 0;

    /* Gli esponenti, tutti multipli di quello del primo che ne ha uno non
     * nullo: si confrontano i prodotti in croce, come in surd_relate(). */
    for (int i = 0; i < m.count; i++) {
        weight[i] = frac_int(0);
        if (m.power[i].num.count == 0) continue;
        if (lead < 0) { lead = i; weight[i] = frac_int(1); continue; }
        Poly a = poly_mul(m.power[i].num, m.power[lead].den), b = poly_mul(m.power[i].den, m.power[lead].num);
        if (a.count != b.count || a.term[0].coef.im.num != 0 || b.term[0].coef.im.num != 0) return 0;
        weight[i] = frac_div(a.term[0].coef.re, b.term[0].coef.re);
        if (failure || !poly_equal(a, poly_mul(b, poly_const(num_frac(weight[i]))))) return 0;
    }
    if (lead < 0) { *out = rat_int(0); return 1; }

    /* Il segno di ln W = somma dei w_p ln p: con D il minimo comune multiplo
     * dei denominatori, è il segno di prodotto dei p^(D w_p) meno 1, cioè
     * del confronto tra i primi con esponente positivo e quelli con
     * esponente negativo. */
    long long common = 1;
    Wide above = {1, 1}, below = {1, 1};
    for (int i = 0; i < m.count; i++) common = lcm_small(common, weight[i].den);
    for (int i = 0; i < m.count && !failure; i++) {
        long long whole = weight[i].num * (common / weight[i].den);
        for (long long k = 0; k < (whole < 0 ? -whole : whole) && !failure; k++)
            if (whole > 0) above = wide_mul(above, (Wide){m.prime[i], 1}); else below = wide_mul(below, (Wide){m.prime[i], 1});
    }
    if (failure) return 0;
    int side = wide_cmp(above, below);
    *out = side < 0 ? rat_add(rat_int(0), m.power[lead], 1) : side > 0 ? m.power[lead] : rat_int(0);
    return 1;
}

/* Calcola left - right (solo left se right è NULL) con i valori assoluti
 * presi secondo `pattern`, e ne prepara in *out l'albero dei segni nella
 * variabile di atomo x, con le condizioni di esistenza. Annota un errore se
 * non è fatta di espressioni razionali e radici quadrate. */
static void sign_fraction(const Node *left, const Node *right, unsigned pattern, int x, SignCase *out) {
    Rat one = rat_int(1);
    out->first = sign_needs;
    out->needs = 0;

    /* Il conto, annotando i divisori incontrati: prima i radicandi, dal più
     * interno, poi la differenza. */
    condition_count = conditions_lost = undefined = 0;
    conditions_on = 1;
    abs_pattern = pattern;
    env_count = 0;
    space_seen = 0;
    for (int i = 0; i < surd_count; i++) surd_value[i] = rat_atom(surd_letter[i]);

    /* 18p-9. Due monomi di potenze: la differenza degli esponenti ha lo
     * stesso segno della differenza dei membri, e non servono lettere. */
    Rat exponent;
    if (right && powers_difference(left, right, &exponent)) {
        conditions_on = 0;
        if (failure) return;
        if (conditions_lost) { fail("troppe condizioni di esistenza in un confronto"); return; }
        out->value = sign_build(exponent, 0, x);
        for (int i = 0; i < condition_count && !failure; i++)
            for (int j = 0; j < conditions[i].count; j++) sign_require(out, (Rat){conditions[i].factor[j], one.num}, 0, 1, x);
        return;
    }
    condition_count = conditions_lost = undefined = 0;
    failure = NULL;
    for (int i = 0; i < surd_count; i++) surd_inside[i] = eval(surd_node[i]->a);

    /* Per l'argomento di un valore assoluto (right è NULL) le condizioni
     * incontrate nei radicandi non contano: i radicandi sono quelli di tutto
     * il confronto, non dell'argomento, e possono contenere proprio il
     * valore assoluto di cui si sta cercando il ramo. Contare l'argomento
     * positivo di un logaritmo sotto radice faceva risultare non definita
     * la radice di log |x| per x negativo. */
    if (!right) {
        condition_count = conditions_lost = 0;
        space_seen = 0;
    }

    /* Le relazioni tra le radici si cercano con l'elenco spento: le
     * divisioni di quel conto non sono dell'enunciato. */
    conditions_on = 0;
    if (!failure) surd_relate();
    conditions_on = 1;
    Rat d = eval(left);
    if (right) d = rat_add(d, eval(right), 1);
    conditions_on = 0;

    /* Una divisione per un'espressione che è zero ovunque: con questa scelta
     * dei segni il confronto non è definito in nessun punto. Capita con
     * |x + |x||, che dove x è negativo vale zero. Lo dice una condizione che
     * non vale mai: lo zero deve essere diverso da zero. */
    if (failure && undefined) {
        failure = NULL;
        undefined = 0;
        out->value = sign_build(rat_int(0), 0, x);
        sign_require(out, rat_int(0), 0, 1, x);
        return;
    }
    if (failure) return;
    if (conditions_lost) { fail("troppe condizioni di esistenza in un confronto"); return; }
    out->value = sign_build(d, surd_count, x);

    /* Le condizioni di esistenza annotate nel conto. Un divisore diverso da
     * zero: ogni suo fattore. Le altre due, che nascono dai logaritmi e
     * dalle potenze che il conto non ha trasformato in lettere (quelli di
     * un numero, per esempio), riguardano il prodotto dei fattori: positivo,
     * oppure non negativo. */
    for (int i = 0; i < condition_count && !failure; i++) {
        Rat product = one;
        for (int j = 0; j < conditions[i].count; j++) {
            if (conditions[i].kind == NEVER_ZERO) sign_require(out, (Rat){conditions[i].factor[j], one.num}, surd_count, 1, x);
            else product = rat_mul(product, (Rat){conditions[i].factor[j], one.num});
        }
        if (conditions[i].kind != NEVER_ZERO) sign_require(out, product, surd_count, conditions[i].kind == ALWAYS_POSITIVE ? 2 : 0, x);
    }
    /* I radicandi non negativi si chiedono al confronto intero (right non è
     * NULL), non all'argomento di un valore assoluto. L'argomento serve a
     * scegliere il ramo del valore assoluto, e lo si calcola prima di sapere
     * quale ramo vale: un radicando che contiene quel valore assoluto, lì, è
     * ancora quello del ramo sbagliato. Chiederlo faceva risultare non
     * definita la radice di |e^x - 2| - 1 dove e^x < 1, che invece lo è. Il
     * confronto intero, nel ramo giusto, chiede comunque tutti i radicandi. */
    for (int i = 0; i < surd_count && right; i++) sign_require(out, surd_inside[i], i, 0, x);

    /* Gli argomenti dei logaritmi comparsi nel conto: positivi. */
    unsigned seen = space_seen;
    for (int s = 0; s < spaces; s++)
        if (seen >> s & 1) sign_require(out, eval(space[s].argument), surd_count, 2, x);
}

/* =============================================================================
 * 18.11 I CONFRONTI PREPARATI, E LA LORO VERITÀ IN UNA RIGA
 * ============================================================================
 *
 * sign_prepare() percorre l'enunciato e prepara ogni confronto per la
 * tabella (SignAtom): un albero dei segni per ogni scelta dei segni dei
 * valori assoluti, una finestra in un enunciato periodico (18p-14), una
 * famiglia di soluzioni sotto un "esiste k" (18p-13). Poi i gradini di ogni
 * spazio diventano confronti nella variabile (18p-8, space_process()).
 * Preparato tutto, sign_truth() dice se l'enunciato vale in una riga della
 * tabella, cioè dati i segni di tutti i polinomi.
 */

/* Mette tra le radici in corso quelle di 2 e di 3, con le loro lettere: i
 * seni e i coseni degli angoli costanti di un enunciato periodico si
 * scrivono con quelle (18p-11). Serve a chi prepara un albero dei segni che
 * non viene da un confronto scritto nell'enunciato. */
static void trig_roots_open(void) {
    abs_count = surd_count = 0;
    for (int i = 0; i < 2; i++) surd_collect(trig_root[i]);
    for (int i = 0; i < surd_count; i++) {
        surd_value[i] = rat_atom(surd_letter[i]);
        surd_inside[i] = eval(surd_node[i]->a);
    }
}

/* I segni del seno e del coseno di un angolo, come alberi dei segni: dicono
 * in quale quarto di giro sta l'angolo, e se è un multiplo di 2 pi. */
typedef struct {
    SignCase sine, cosine;
} FamilyAngle;

/* Una famiglia preparata per la tabella (18p-13): gli angoli che dicono se
 * la variabile sta in uno dei suoi punti o intervalli. below è l'angolo
 * A = 2 pi (x - low) / T, above è B = 2 pi (high - x) / T (non usato per un
 * punto), hole[i] è 2 pi (x - hole[i]) / T. wide dice che l'intervallo è più
 * lungo di mezzo periodo, full che è lungo proprio un periodo (allora copre
 * tutto, tranne al più il punto in cui comincia e finisce); hole_counts[i]
 * che quel punto tolto sta nell'intervallo dello stesso k, il solo caso in
 * cui toglie qualcosa. */
typedef struct {
    const Formula *owner;  /* il quantificatore di cui la famiglia è un pezzo */
    Family family;
    FamilyAngle below, above, hole[MAX_LATTICE_HOLES];
    int wide, full;
    int hole_counts[MAX_LATTICE_HOLES];
} FamilyLeaf;

/* Le famiglie dell'enunciato in corso, di tutti i suoi quantificatori su un
 * intero: family_truth() prende quelle del suo (owner). */
static FamilyLeaf family_leaf[MAX_LATTICE];
static int family_leaves;

/* Prepara in *out i segni del seno e del coseno di
 * direction 2 pi (x - e) / T, dove e = alpha + k T è un'espressione della
 * famiglia e direction è 1 o -1.
 *
 * L'angolo è n u + psi con u = g x l'angolo dell'enunciato, n intero e
 * psi = -direction 2 pi alpha / T un angolo costante. Di psi serve la
 * direzione (cos psi, sin psi) a meno di un fattore positivo: la parte che
 * è un multiplo di pi la dà trig_constant(); ogni arcotangente di un
 * razionale m, con coefficiente intero p, la ruota di (1 + i m)^p, perché
 * cos(arctan m) + i sin(arctan m) è 1 + i m diviso per un numero positivo. */
static void family_angle(const Node *e, int k, int direction, int x, FamilyAngle *out) {
    Frac tau, turn = frac_int(0);
    Rat alpha, real = rat_int(1), imaginary = rat_int(0), cb, sb, cn, sn;
    int pi = atom_var(VAR_PI);
    out->sine.first = out->cosine.first = sign_needs;
    out->sine.needs = out->cosine.needs = 0;
    if (!family_period(e, k, &tau, &alpha)) { if (!failure) fail(SIGN_SHAPE); return; }
    if (tau.num < 0) tau.num = -tau.num;
    Frac multiple = frac_div(frac_div(frac_int(2 * direction), tau), trig_scale), scale = frac_div(frac_int(-2 * direction), tau);
    if (multiple.den != 1) { fail(SIGN_SHAPE); return; }

    /* psi, un termine di alpha alla volta. */
    Frac den = alpha.den.term[0].coef.re;
    for (int i = 0; i < alpha.num.count && !failure; i++) {
        const Term *t = &alpha.num.term[i];
        const Atom *atom = t->mono.count == 1 ? &atoms[t->mono.factor[0].atom] : NULL;
        Frac weight = frac_mul(frac_div(t->coef.re, den), scale);
        Num slope;
        if (!atom || t->coef.im.num != 0 || frac_cmp(t->mono.factor[0].exp, frac_int(1)) != 0) { fail(SIGN_SHAPE); return; }
        if (t->mono.factor[0].atom == pi) { turn = frac_add(turn, weight); continue; }
        if (atom->kind != ATOM_ATAN || weight.den != 1 || !rat_number(atan_args[atom->id], &slope) || slope.im.num != 0) { fail(SIGN_SHAPE); return; }
        Rat m = rat_frac(weight.num < 0 ? frac_neg(slope.re) : slope.re);
        for (long long step = 0; step < (weight.num < 0 ? -weight.num : weight.num); step++) {
            Rat was = real;
            real = rat_add(real, rat_mul(imaginary, m), 1);
            imaginary = rat_add(imaginary, rat_mul(was, m), 0);
        }
    }
    if (failure || !trig_constant(turn, &cb, &sb)) { if (!failure) fail("una famiglia di soluzioni con un angolo che non è un multiplo di 15 gradi"); return; }

    /* sin(n u + psi) e cos(n u + psi), con le formule di addizione. */
    Rat cosine = rat_add(rat_mul(cb, real), rat_mul(sb, imaginary), 1), sine = rat_add(rat_mul(sb, real), rat_mul(cb, imaginary), 0);
    trig_multiple(multiple.num, &cn, &sn);
    out->sine.value = sign_build(rat_add(rat_mul(sn, cosine), rat_mul(cn, sine), 0), surd_count, x);
    out->cosine.value = sign_build(rat_add(rat_mul(cn, cosine), rat_mul(sn, sine), 1), surd_count, x);
}

/* Per sign_prepare: prepara il pezzo d del quantificatore owner. context
 * punta all'atomo della lettera della tabella. La lunghezza dell'intervallo
 * rispetto al periodo, e se un punto tolto sta nell'intervallo dello stesso
 * k, si decidono con i numeri, per k = 0 e k = 1: dove non è certo, il pezzo
 * non è trattato. */
static void family_prepare(const Formula *owner, const Formula *d, void *context) {
    int x = *(const int *)context, none = 0, side = 0;
    Range zero = {0, 0}, one = {1, 1};
    if (failure) return;
    if (family_leaves == MAX_LATTICE) { fail("troppe famiglie di soluzioni in un enunciato"); return; }
    FamilyLeaf *leaf = &family_leaf[family_leaves++];
    const Family *family = &leaf->family;
    leaf->owner = owner;
    if (!family_read(d, sign_name, owner->variable, owner->kind == F_FORALL, &leaf->family)) { fail(SIGN_SHAPE); return; }

    /* Le radici di 2 e di 3 servono ai seni e ai coseni degli angoli
     * costanti, come in ogni confronto di un enunciato periodico. */
    trig_roots_open();
    trig_live = 1;
    family_angle(family->low, family->k, 1, x, &leaf->below);
    if (!family->single && !failure) {
        /* L'intervallo deve stare in un periodo; wide se supera la metà. Un
         * intervallo lungo proprio mezzo periodo va bene in tutti e due i
         * modi (i due seni sono uguali), e uno lungo proprio un periodo è
         * un caso a sé (full); ma con i numeri un'uguaglianza non la si
         * vede mai: lì decide il conto esatto, quando gli estremi sono
         * multipli di pi. */
        Frac tau, slope, turns = frac_int(0);
        Rat low_part, high_part;
        Range low = node_range(family->low, family->k, zero, &none), width = range_sub(node_range(family->high, family->k, zero, &none), low);
        Range period = range_sub(node_range(family->low, family->k, one, &none), low);
        if (range_side(period, &side) && side < 0) period = range_neg(period);
        int positive = range_side(width, &side) && side > 0, inside = range_side(range_sub(period, width), &side) && side > 0;
        int exact = family_period(family->low, family->k, &tau, &low_part) && family_period(family->high, family->k, &tau, &high_part) &&
                    trig_affine(rat_add(high_part, low_part, 1), &slope, &turns) && slope.num == 0;
        if (tau.num < 0) tau.num = -tau.num;
        int half = exact && frac_cmp(frac_add(turns, turns), tau) == 0;
        leaf->full = exact && frac_cmp(turns, tau) == 0;
        leaf->wide = 0;
        if (!leaf->full && !half) {
            if (!positive || !inside) fail("un intervallo di una famiglia di soluzioni non può essere più lungo del periodo");
            else if (!range_side(range_sub(range_add(width, width), period), &side)) fail("non so dire se un intervallo di una famiglia di soluzioni supera mezzo periodo");
            else leaf->wide = side > 0;
        }
        family_angle(family->high, family->k, -1, x, &leaf->above);
    }
    for (int i = 0; i < family->holes && !failure; i++) {
        Range hole = node_range(family->hole[i], family->k, zero, &none);
        int after = range_side(range_sub(hole, node_range(family->low, family->k, zero, &none)), &side) ? side : 0;
        int before = range_side(range_sub(node_range(family->high, family->k, zero, &none), hole), &side) ? side : 0;
        if (after == 0 || before == 0) { fail("un punto tolto proprio sull'estremo di un intervallo: non so dire se conta"); break; }
        leaf->hole_counts[i] = after > 0 && before > 0;
        family_angle(family->hole[i], family->k, 1, x, &leaf->hole[i]);
    }
    trig_live = 0;
    surd_count = 0;
}

/* Ritorna 1 se in node compare una funzione goniometrica della variabile. */
static int node_has_trig(const Node *node) {
    if (!node) return 0;
    if (node->kind == N_CALL && node->op >= FN_SIN && node->op <= FN_COT && node_uses_letter(node->a, sign_name)) return 1;
    return node_has_trig(node->a) || node_has_trig(node->b) || node_has_trig(node->c);
}

/* 18p-14. LE FINESTRE: UNA CONDIZIONE PERIODICA RISTRETTA A UN INTERVALLO
 *
 * In 0 \le x \le 2\pi \land \sin x > \frac{1}{2} la variabile compare anche
 * fuori dalle funzioni goniometriche. Un confronto così, tra la variabile e
 * un multiplo di pi, qui si chiama finestra. Non è periodico, e la lettera
 * t = tan(u / 2) non lo vede: t è la stessa in u e in u + 2 pi. Ma la
 * tabella in t descrive bene ogni giro; da un giro all'altro cambia solo la
 * finestra. Quindi la tabella si legge un giro alla volta: nel giro numero
 * j l'angolo è u = u_0 + 2 pi j, con u_0 tra -pi (escluso) e pi (compreso).
 *
 * Una finestra x <= rho pi è u <= gamma, con gamma = g rho pi. Si scrive
 * gamma = gamma_0 + 2 pi h, con gamma_0 tra -pi (escluso) e pi (compreso):
 * h è il giro in cui cade l'estremo. Allora:
 *
 *   - in un giro j < h tutti gli angoli stanno sotto gamma, in un giro
 *     j > h tutti sopra;
 *   - nel giro h, u - gamma = u_0 - gamma_0. Sull'intervallo da -pi a pi la
 *     tangente dell'angolo metà cresce, quindi u_0 - gamma_0 ha il segno di
 *     t - tan(gamma_0 / 2); e tan(gamma_0 / 2) = sin gamma_0 / (1 + cos gamma_0)
 *     (formule di bisezione), con 1 + cos gamma_0 positivo: è il segno di
 *     t (1 + cos gamma_0) - sin gamma_0, un polinomio di primo grado in t;
 *   - se gamma_0 = pi, su ogni riga della tabella u_0 è più piccolo, e nel
 *     punto u_0 = pi, quello calcolato a parte, i due sono uguali.
 *
 * I giri da leggere vanno da quello prima del più basso h a quello dopo il
 * più alto: più in là le finestre non cambiano più, e il primo e l'ultimo
 * giro letti valgono per tutti quelli prima e per tutti quelli dopo. Un
 * insieme di soluzioni che non è vuoto in uno di questi due giri si ripete
 * all'infinito da una parte sola: non è né limitato né periodico, e il
 * programma dice che non lo sa scrivere.
 *
 * Che cosa resta fuori: un estremo che non è un multiplo razionale di pi
 * (x < 1 chiederebbe la tangente di 1/2), o lo è ma non di 15 gradi.
 */

/* Prepara la finestra f, un confronto senza funzioni goniometriche in cui
 * compare la variabile di un enunciato periodico, nel posto atom di
 * sign_atom[]. x è l'atomo della lettera t. Annota un errore se la
 * differenza dei due membri non è a x + b pi con a diverso da zero. */
static void window_prepare(const Formula *f, SignAtom *atom, int x) {
    Frac slope, turn;
    Rat cosine, sine, difference = rat_add(eval(f->left), eval(f->right), 1);
    if (failure || !trig_affine(difference, &slope, &turn) || slope.num == 0) { if (!failure) fail(SIGN_SHAPE); return; }

    /* gamma in giri di pi: whole = rest + 2 home, con rest tra -1 (escluso)
     * e 1 (compreso). home è la parte intera superiore di (whole - 1) / 2. */
    Frac whole = frac_mul(frac_neg(frac_div(turn, slope)), trig_scale);
    if (failure || whole.num > 1000000 || whole.num < -1000000 || whole.den > 1000000) { fail("una finestra con un estremo troppo grande"); return; }
    long long top = whole.num - whole.den, bottom = 2 * whole.den;
    atom->home = top >= 0 ? (top + bottom - 1) / bottom : -((-top) / bottom);
    Frac rest = frac_add(whole, frac_int(-2 * atom->home));
    int at_end = rest.num == rest.den;
    atom->window = 1;
    atom->direction = slope.num > 0 ? 1 : -1;
    atom->inner_count = 0;
    if (!windows || atom->home < window_low) window_low = atom->home;
    if (!windows || atom->home > window_high) window_high = atom->home;
    windows++;

    /* Il segno di u_0 - gamma_0: nel punto u_0 = pi, oppure sulle righe. */
    SignCase *edge = &atom->by_pattern[0];
    trig_roots_open();
    edge->first = sign_needs;
    edge->needs = 0;
    if (trig_at_pi) edge->value = sign_constant(at_end ? 0 : 1, x);
    else if (at_end) edge->value = sign_constant(-1, x);
    else if (!trig_constant(rest, &cosine, &sine)) { if (!failure) fail("una finestra con un estremo che non è un multiplo di 15 gradi"); }
    else edge->value = sign_build(rat_add(rat_mul(rat_atom(trig_letter), rat_add(rat_int(1), cosine, 0)), sine, 1), surd_count, x);
    surd_count = 0;
}

/* Prepara i confronti dell'enunciato f nella variabile di atomo x: riempie
 * sign_atom[] e sign_poly[]. Un quantificatore su un intero è una foglia: le
 * sue famiglie si preparano con family_prepare() (18p-13). In un enunciato
 * periodico un confronto senza funzioni goniometriche della variabile è una
 * finestra (18p-14). Annota un errore se un confronto non è tra espressioni
 * che la tabella tratta. */
static void sign_prepare(const Formula *f, int x) {
    if (failure) return;
    if (family_owner(f)) { family_each(f, f->a, family_prepare, &x); return; }
    if (f->kind != F_EQUAL && f->kind != F_DISTINCT && f->kind != F_LESS && f->kind != F_LESS_EQ) {
        sign_prepare(f->a, x);
        if (f->b) sign_prepare(f->b, x);
        return;
    }
    if (sign_atoms == MAX_SIGN_ATOMS) { fail("troppi confronti in un enunciato per la tabella dei segni"); return; }
    SignAtom *atom = &sign_atom[sign_atoms++];
    atom->source = f;
    atom->identity = atom->window = 0;
    if (trig_on && !node_has_trig(f->left) && !node_has_trig(f->right) && (node_uses_letter(f->left, sign_name) || node_uses_letter(f->right, sign_name))) {
        window_prepare(f, atom, x);
        return;
    }

    /* I valori assoluti e le radici; poi, per ogni scelta dei segni dei
     * valori assoluti, il confronto e i loro argomenti. */
    abs_count = surd_count = 0;
    abs_collect(f->left);
    abs_collect(f->right);

    /* In un enunciato periodico servono le radici di 2 e di 3, per i seni e
     * i coseni degli angoli costanti (18p-11). */
    for (int i = 0; i < 2 && trig_on; i++) surd_collect(trig_root[i]);
    surd_collect(f->left);
    surd_collect(f->right);
    atom->inner_count = abs_count;
    alias_collect(f->left, f);
    alias_collect(f->right, f);
    space_live = 1;
    trig_live = trig_on;
    for (unsigned pattern = 0; pattern < 1u << abs_count && !failure; pattern++) {
        sign_fraction(f->left, f->right, pattern, x, &atom->by_pattern[pattern]);
        for (int i = 0; i < abs_count && !failure; i++) sign_fraction(abs_node[i]->a, NULL, pattern, x, &atom->inner[i][pattern]);
    }
    abs_count = surd_count = space_live = trig_live = aliases = 0;
}

/* Aggiunge all'enunciato il confronto tra left e right, lo prepara per la
 * tabella e lo ritorna: serve ai gradini degli spazi, il cui confronto con
 * la lettera è un confronto nella variabile (18p-8). Del confronto si usa
 * solo il segno di left - right. */
static const Formula *sign_threshold(Node *left, Node *right, int x) {
    Formula *f = formula_node(F_EQUAL, NULL, NULL, "");
    f->left = left;
    f->right = right;
    sign_prepare(f, x);
    return f;
}

/* Ritorna un nodo che vale base elevato a power, con base razionale
 * positivo e power intero; NULL se i numeri sono troppo grandi. */
static Node *node_power(Frac base, long long power) {
    __int128 top = 1, bottom = 1;
    for (long long i = 0; i < (power < 0 ? -power : power); i++)
        if (__builtin_mul_overflow(top, (__int128)(power < 0 ? base.den : base.num), &top) || __builtin_mul_overflow(bottom, (__int128)(power < 0 ? base.num : base.den), &bottom) ||
            top > LLONG_MAX / 4 || bottom > LLONG_MAX / 4) return NULL;
    return bottom == 1 ? node_num((long long)top) : node_new(N_DIV, node_num((long long)top), node_num((long long)bottom));
}

/* Ritorna un intervallo che contiene la sola radice del polinomio element
 * tra low e high, stretta per bisezione. A ogni passo il segno del polinomio
 * nel punto medio si calcola con gli intervalli (schema di Horner): finché è
 * certo si sa da che parte sta la radice, e quando non lo è più ci si
 * ferma, con un intervallo che la contiene ancora. */
static Range root_range(const Uni *element, Wide low_end, Wide high_end) {
    double low = range_ratio(low_end.num, low_end.den).low, high = range_ratio(high_end.num, high_end.den).high;
    int at_low = uni_sign_at(element, low_end), side = 0;
    for (int round = 0; round < 80; round++) {
        double middle = (low + high) / 2;
        Range value = {0, 0}, point = {middle, middle};
        for (int i = element->degree; i >= 0; i--) value = range_add(range_mul(value, point), range_ratio(element->c[i], 1));
        if (!range_side(value, &side)) break;
        if (side == at_low) low = middle; else high = middle;
    }
    return range_wide(low, high);
}

/* Ritorna un intervallo che contiene il gradino step. */
static Range step_range(const Step *step) {
    return step->exact ? range_ratio(step->low.num, step->low.den) : root_range(&step->element, step->low, step->high);
}

/* Se r = p^k con k intero mette k in *power e ritorna 1. Per p = 0, che
 * sta per il numero e, lo è solo r = 1. */
static int power_of_prime(Wide r, long long p, long long *power) {
    __int128 rest = r.num == 1 ? r.den : r.num;
    *power = 0;
    if (r.num != 1 && r.den != 1) return 0;
    if (p == 0) return rest == 1;
    for (; rest % p == 0; rest /= p) *power += r.num == 1 ? -1 : 1;
    return rest == 1;
}

/* Se il gradino step, che non è razionale, è la radice n-esima positiva di
 * un razionale positivo q, cioè se il suo polinomio è a x^n - b, mette q in
 * *under e ritorna n; altrimenti ritorna 0. */
static long long step_pure(const Step *step, Wide *under) {
    const Uni *q = &step->element;
    for (int i = 1; i < q->degree; i++)
        if (q->c[i] != 0) return 0;
    if (q->degree < 2 || step->high.num <= 0) return 0;
    *under = wide_make(-q->c[0], q->c[q->degree]);
    return under->num > 0 ? q->degree : 0;
}

/* Scrive in text, di size byte, il gradino step in LaTeX: il razionale, o
 * la radice con i radicali se il suo polinomio ha grado due. smaller dice
 * se delle due radici è la più piccola. Annota un errore se il gradino è
 * una radice senza scrittura. */
static void step_latex(const Step *step, int smaller, char *text, size_t size) {
    text[0] = '\0';
    if (step->exact) wide_latex(step->low, text, size);
    else if (!quadratic_latex(&step->element, smaller, text, size)) fail("un esponenziale o un logaritmo uguale a un numero che non so scrivere");
}

/* 18p-8. Trova i gradini dello spazio s, le radici reali dei polinomi nella
 * sua lettera, e per ognuno prepara il confronto nella variabile che dice
 * se la lettera gli sta sopra. name e x sono la variabile, come lettera e
 * come atomo. Usa le tabelle dei punti (sign_base[], sign_point[]), che poi
 * restano libere per lo spazio successivo. */
static void space_process(int s, int name, int x) {
    Space *sp = &space[s];
    sign_points(s);
    sp->steps = 0;
    for (int i = 0; i < sign_points_count && !failure; i++) {
        Critical *point = &sign_point[i];

        /* Un esponenziale è positivo: i gradini da zero in giù non lo
         * riguardano. Una radice irrazionale va stretta finché non si sa da
         * che parte dello zero sta. */
        if (sp->kind == SPACE_EXP) {
            while (!failure && !point->exact && point->low.num <= 0 && point->high.num >= 0) point_refine(point);
            if (point->high.num <= 0) continue;
        }
        if (sp->steps == MAX_STEPS) { fail("troppe radici di un polinomio in un esponenziale o in un logaritmo"); return; }
        Step *step = &sp->step[sp->steps++];
        *step = (Step){point->exact, point->low, point->high, {0, {0}}, NULL, -1};
        if (!point->exact) step->element = sign_base[point->element];
    }

    /* I confronti, dopo aver copiato tutti i gradini: prepararli riusa le
     * tabelle dei punti. */
    for (int j = 0; j < sp->steps && !failure; j++) {
        Step *step = &sp->step[j];
        char value[64], text[96];
        long long power;
        Wide pure;
        int smaller = j + 1 < sp->steps && !step->exact && !sp->step[j + 1].exact && uni_equal(&step->element, &sp->step[j + 1].element);
        Node *variable = node_new(N_VAR, NULL, NULL);
        variable->name = name;

        long long index = step->exact ? 1 : step_pure(step, &pure);
        if (sp->kind == SPACE_EXP && index && power_of_prime(step->exact ? step->low : pure, sp->prime, &power)) {
            /* p^(x/L) = p^(k/n): x = L k / n, un razionale. Capita con n > 1
             * quando il gradino è la radice n-esima di una potenza di p. */
            Frac at = frac_make((__int128)sp->scale * power, index);
            step->above = sign_threshold(variable, at.den == 1 ? node_num(at.num) : node_new(N_DIV, node_num(at.num), node_num(at.den)), x);
        } else if (sp->kind == SPACE_EXP) {
            /* x = L log_p r, un numero che non è radice di un polinomio. */
            Range number = range_mul(range_ratio(sp->scale, 1), range_ln(step_range(step)));
            if (sp->prime) number = range_div(number, range_ln(range_ratio(sp->prime, 1)));
            step_latex(step, smaller, value, sizeof value);
            /* L'argomento di una funzione senza parentesi è un solo fattore
             * (capitolo 9): \log_{5} 2\sqrt{15} si rileggerebbe come
             * (\log_{5} 2) \sqrt{15}. Senza parentesi resta solo un intero. */
            int wrap = value[strspn(value, "0123456789")] != '\0';
            if (sp->prime) snprintf(text, sizeof text, "%.0lld\\log_{%lld} %s%s%s", sp->scale == 1 ? 0 : sp->scale, sp->prime, wrap ? "\\left(" : "", value, wrap ? "\\right)" : "");
            else snprintf(text, sizeof text, "%.0lld\\ln %s%s%s", sp->scale == 1 ? 0 : sp->scale, wrap ? "\\left(" : "", value, wrap ? "\\right)" : "");

            /* Lo stesso numero come frazione esatta, quando il gradino è un
             * razionale: L ln r / ln p. */
            Rat exact = rat_int(0);
            int plain = step->exact && step->low.num < LLONG_MAX / 4 && step->low.den < LLONG_MAX / 4 && !failure;
            if (plain) {
                exact = rat_mul(rat_int(sp->scale), logarithm_of_positive(rat_frac((Frac){(long long)step->low.num, (long long)step->low.den})));
                if (sp->prime) exact = rat_div(exact, logarithm_of_positive(rat_int(sp->prime)));
            }
            if (!failure) step->kappa = sign_column_kappa(number, text, plain ? &exact : NULL);
        } else if (!step->exact || (!sp->natural && (step->low.den > 2 || (step->low.den == 2 && sp->base.den != 1)))) {
            fail("un logaritmo uguale a un numero irrazionale, o una potenza della base che non so scrivere");
        } else if (sp->natural && step->low.num != 0) {
            /* ln f = r con r diverso da zero: f = e^r, che non è radice di un
             * polinomio. Lo si tratta quando f = a x + c con a positivo:
             * allora x = (e^r - c) / a è un punto della tabella. */
            Frac slope, shift;
            space_live = 1;
            int affine = rat_affine_in(eval(sp->argument), x, &slope, &shift) && slope.num > 0;
            space_live = 0;
            if (!affine) { fail("un logaritmo naturale uguale a un numero diverso da zero è trattato solo per un argomento di primo grado, crescente"); return; }
            char power_text[48] = "e", top[96];
            if (step->low.den != 1) snprintf(power_text, sizeof power_text, "e^{%s\\frac{%lld}{%lld}}", step->low.num < 0 ? "-" : "", (long long)(step->low.num < 0 ? -step->low.num : step->low.num), (long long)step->low.den);
            else if (step->low.num != 1) snprintf(power_text, sizeof power_text, "e^{%lld}", (long long)step->low.num);
            if (shift.num == 0) snprintf(top, sizeof top, "%s", power_text);
            else if (shift.den == 1) snprintf(top, sizeof top, "%s %c %lld", power_text, shift.num < 0 ? '+' : '-', (long long)(shift.num < 0 ? -shift.num : shift.num));
            else snprintf(top, sizeof top, "%s %c \\frac{%lld}{%lld}", power_text, shift.num < 0 ? '+' : '-', (long long)(shift.num < 0 ? -shift.num : shift.num), (long long)shift.den);
            if (slope.num == slope.den) snprintf(text, sizeof text, "%s", top);
            else if (slope.den == 1) snprintf(text, sizeof text, "\\frac{%s}{%lld}", top, (long long)slope.num);
            else snprintf(text, sizeof text, "\\frac{%lld\\left(%s\\right)}{%lld}", (long long)slope.den, top, (long long)slope.num);
            Range number = range_div(range_sub(range_exp(range_ratio(step->low.num, step->low.den)), range_ratio(shift.num, shift.den)), range_ratio(slope.num, slope.den));

            /* Come frazione esatta: (e^r - c) / a, con e un atomo. */
            Rat exact = rat_div(rat_add((Rat){poly_term((Term){num_int(1), mono_atom(atom_var('e'), (Frac){(long long)step->low.num, (long long)step->low.den})}), poly_const(num_int(1))}, rat_frac(shift), 1), rat_frac(slope));
            step->kappa = sign_column_kappa(number, text, &exact);
        } else {
            /* log_b f = k / m: f = b^(k/m), con m = 1 oppure 2. Con m = 2 è
             * b^((k - 1)/2) per la radice di b. */
            long long k = (long long)step->low.num, half = step->low.den == 2 ? (k - 1) / 2 - ((k - 1) % 2 < 0) : k;
            Node *constant = sp->natural ? node_num(1) : node_power(sp->base, half);
            if (!constant) { fail(SIGN_LIMIT); return; }
            if (step->low.den == 2) constant = node_new(N_MUL, constant, node_call(FN_ROOT, node_num(sp->base.num), node_num(2)));
            step->above = sign_threshold((Node *)sp->argument, constant, x);
        }
    }
}

/* Ritorna il segno dell'espressione c dove i polinomi hanno i segni di
 * sign[]; mette 0 in *defined, che chi chiama ha messo a 1, se lì non è
 * definita. */
static int sign_of_case(const SignCase *c, const int *sign, int *defined) {
    for (int i = 0; i < c->needs; i++) {
        int value = sign_value(sign_need[c->first + i].node, sign, defined), strict = sign_need[c->first + i].strict;
        if (strict == 1 ? value == 0 : strict == 2 ? value <= 0 : value < 0) *defined = 0;
    }
    return sign_value(c->value, sign, defined);
}

/* Ritorna 1 se l'angolo angle è un multiplo di 2 pi dove i polinomi hanno i
 * segni di sign[]: il seno è zero e il coseno positivo. */
static int family_at_zero(const FamilyAngle *angle, const int *sign) {
    int defined = 1;
    return sign_of_case(&angle->sine, sign, &defined) == 0 && sign_of_case(&angle->cosine, sign, &defined) > 0;
}

/* Ritorna 1 se il quantificatore su un intero f è vero dove i polinomi
 * hanno i segni di sign[]: per "esiste" se la variabile sta in una delle
 * sue famiglie, per "per ogni k, x diverso da ..." se non sta in nessuna.
 * Le regole sono quelle scritte in testa a 18p-13. */
static int family_truth(const Formula *f, const int *sign) {
    int any = 0;
    for (int i = 0; i < family_leaves; i++) {
        const FamilyLeaf *leaf = &family_leaf[i];
        int defined = 1, in = family_at_zero(&leaf->below, sign);
        if (leaf->owner != f) continue;
        if (!leaf->family.single) {
            int low = sign_of_case(&leaf->below.sine, sign, &defined), high = sign_of_case(&leaf->above.sine, sign, &defined);
            if (leaf->full) in = !in || leaf->family.low_closed || leaf->family.high_closed;
            else in = (in && leaf->family.low_closed) || (family_at_zero(&leaf->above, sign) && leaf->family.high_closed) ||
                      (leaf->wide ? low > 0 || high > 0 : low > 0 && high > 0);
            for (int h = 0; h < leaf->family.holes; h++)
                if (leaf->hole_counts[h] && family_at_zero(&leaf->hole[h], sign)) in = 0;
        }
        any |= in;
    }
    return f->kind == F_EXISTS ? any : !any;
}

/* Ritorna il segno di left - right per il confronto f dove i polinomi di
 * sign_poly[] hanno i segni di sign[]; mette 0 in *defined, che chi chiama ha
 * messo a 1, se lì uno dei due membri non è definito.
 *
 * Prima la scelta dei segni dei valori assoluti, da quelli più interni: uno
 * ha il segno cambiato dove il suo argomento è negativo. Poi il segno della
 * differenza in quella scelta. */
int sign_compare(const Formula *f, const int *sign, int *defined) {
    const SignAtom *atom = NULL;
    unsigned pattern = 0;
    for (int i = 0; i < sign_atoms; i++)
        if (sign_atom[i].source == f) atom = &sign_atom[i];
    if (!atom) { *defined = 0; return 0; }

    /* 18p-14. Una finestra: sotto o sopra il suo estremo in tutti i giri
     * tranne quello in cui l'estremo cade. */
    if (atom->window) {
        int side = window_turn < atom->home ? -1 : window_turn > atom->home ? 1 : sign_of_case(&atom->by_pattern[0], sign, defined);
        return side * atom->direction;
    }
    for (int i = 0; i < atom->inner_count; i++)
        if (sign_of_case(&atom->inner[i][pattern], sign, defined) < 0) pattern |= 1u << i;
    return sign_of_case(&atom->by_pattern[pattern], sign, defined);
}

/* Ritorna 1 se l'enunciato f, senza quantificatori, è vero dove i polinomi
 * di sign_poly[] hanno i segni di sign[] (-1, 0 o 1), altrimenti 0. */
int sign_truth(const Formula *f, const int *sign) {
    if (family_owner(f)) return family_truth(f, sign);
    switch (f->kind) {
    case F_AND:     return sign_truth(f->a, sign) && sign_truth(f->b, sign);
    case F_OR:      return sign_truth(f->a, sign) || sign_truth(f->b, sign);
    case F_IMPLIES: return !sign_truth(f->a, sign) || sign_truth(f->b, sign);
    case F_IFF:     return sign_truth(f->a, sign) == sign_truth(f->b, sign);
    case F_NOT:     return !sign_truth(f->a, sign);
    default:        break;
    }

    /* Un confronto: definito, e con il segno giusto. */
    int defined = 1, value = sign_compare(f, sign, &defined);
    if (!defined) return 0;
    switch (f->kind) {
    case F_EQUAL:    return value == 0;
    case F_DISTINCT: return value != 0;
    case F_LESS:     return value < 0;
    default:         return value <= 0;
    }
}

/* =============================================================================
 * 18.12 IL CONTROLLO CON I NUMERI
 * ============================================================================
 *
 * Il controllo indipendente delle righe della tabella (18p-2), fatto senza
 * polinomi in una variabile e senza radici: il valore di una riga si
 * sostituisce nell'enunciato e si calcola, con il conto esatto quando è
 * razionale (sign_holds_at()), con gli intervalli del capitolo 24 quando non
 * lo è o l'enunciato è periodico (range_truth()). Ciò che dicono i due conti
 * è solo "vale", "non vale" o "non so": il segno di un numero con radici si
 * stringe tra due razionali (number_sign()), un'uguaglianza vista con gli
 * intervalli si può solo trovare compatibile, a meno che i due membri siano
 * la stessa funzione (formula_identity()). Chi ricontrolla usa
 * table_agrees().
 */

/* Mette in *low e *high due razionali tra cui sta il valore di p, che deve
 * essere un numero fatto di razionali e di radici quadrate di interi: una
 * somma di termini q sqrt(m). Ogni radice è presa tra k / 2^bits e
 * (k + 1) / 2^bits, con k la parte intera di sqrt(m) 2^bits. Ritorna 0 se p
 * non ha questa forma o se i numeri escono dai limiti. */
static int number_bounds(Poly p, int bits, Wide *low, Wide *high) {
    *low = *high = (Wide){0, 1};
    for (int t = 0; t < p.count && !failure; t++) {
        const Term *term = &p.term[t];
        if (term->coef.im.num != 0) return 0;

        /* Il termine: un razionale per la radice di un intero. Un primo con
         * esponente e = w + 1/2 dà p^w fuori dalla radice e p dentro. */
        Wide rational = {term->coef.re.num, term->coef.re.den};
        __int128 under = 1;
        for (int f = 0; f < term->mono.count && !failure; f++) {
            const Atom *atom = &atoms[term->mono.factor[f].atom];
            Frac e = term->mono.factor[f].exp;
            if (atom->kind != ATOM_POW || atom->base != BASE_PRIME || atom->exponent.count != 0 || e.den > 2) return 0;
            long long whole = frac_floor(e);
            for (long long i = 0; i < (whole < 0 ? -whole : whole) && !failure; i++)
                rational = wide_mul(rational, whole < 0 ? (Wide){1, atom->id} : (Wide){atom->id, 1});
            if (e.den == 2) under *= atom->id;
            if (under >= (__int128)1 << 40) return 0;
        }
        if (failure) return 0;

        /* La radice tra due razionali vicini; se è esatta, i due coincidono.
         * Con un razionale negativo davanti i due limiti si scambiano. */
        __int128 scaled = under << (2 * bits), root = wide_isqrt(scaled), unit = (__int128)1 << bits;
        Wide below = wide_mul(rational, wide_make(root, unit)), above = wide_mul(rational, wide_make(root + (root * root != scaled), unit));
        *low = wide_add(*low, rational.num < 0 ? above : below);
        *high = wide_add(*high, rational.num < 0 ? below : above);
    }
    return !failure;
}

/* Mette in *side il segno del numero r e ritorna 1; ritorna 0 se non riesce
 * a stabilirlo. r può contenere radici quadrate di interi.
 *
 * Il segno di un numero con radici si trova stringendolo tra due razionali:
 * prima o poi i due hanno lo stesso segno, a meno che il numero sia zero. Lo
 * zero va quindi riconosciuto prima, con il test del capitolo 12, che per le
 * radici di interi è esatto. La precisione cresce fino a 40 cifre binarie;
 * se non basta, la risposta è "non so". È un conto diverso da quello della
 * tabella dei segni, che non approssima mai: per questo vale come controllo. */
int number_sign(Rat r, int *side) {
    Num value;

    /* Un numeratore senza termini è zero, qualunque cosa ci sia sotto: è
     * così che si riconosce lo zero di un'espressione con logaritmi, dove il
     * denominatore non si semplifica. */
    if (r.num.count == 0) { *side = 0; return 1; }
    if (rat_number(r, &value)) {
        *side = (value.re.num > 0) - (value.re.num < 0);
        return value.im.num == 0;
    }
    for (int bits = 8; bits <= 40 && !failure; bits += 8) {
        Wide low[2], high[2];
        if (!number_bounds(r.num, bits, &low[0], &high[0]) || !number_bounds(r.den, bits, &low[1], &high[1])) return 0;
        int above = low[0].num > 0 ? 1 : high[0].num < 0 ? -1 : 0, below = low[1].num > 0 ? 1 : high[1].num < 0 ? -1 : 0;
        if (above && below) { *side = above * below; return 1; }

        /* Dopo il primo giro si sa che r è un numero di questa forma, e si
         * può chiedere se è zero. */
        if (bits == 8 && poly_vanishes(r.num)) { *side = 0; return 1; }
    }
    return 0;
}

/* Ritorna 1 se le condizioni di esistenza annotate in conditions[] valgono
 * tutte di sicuro; 0 se una di sicuro non vale, e allora mette 1 in
 * *broken; 0 anche se di una non si riesce a dire. Ogni condizione riguarda
 * un prodotto di numeri: il segno di ogni fattore lo dà number_sign(),
 * esatto, oppure il suo intervallo. */
static int conditions_hold(int *broken) {
    for (int i = 0; i < condition_count; i++) {
        int product = 1;
        for (int j = 0; j < conditions[i].count; j++) {
            int side = 0;
            Rat factor = {conditions[i].factor[j], poly_const(num_int(1))};
            if (!number_sign(factor, &side) && !range_side(poly_range(factor.num), &side)) { failure = NULL; return 0; }
            product *= side;
        }
        failure = NULL;
        if (conditions[i].kind == NEVER_ZERO ? product == 0 : conditions[i].kind == ALWAYS_POSITIVE ? product <= 0 : product < 0) { *broken = 1; return 0; }
    }
    return 1;
}

/* Ritorna 1 se la condizione f, senza quantificatori, vale quando la
 * variabile di nome name è il razionale value, calcolando ogni confronto
 * direttamente con i numeri: un confronto in cui un'espressione non è
 * definita non vale. È il controllo indipendente della tabella dei segni:
 * non usa né polinomi in una variabile né radici.
 *
 * Chi chiama azzera `failure` prima. Se un conto si ferma a un limite del
 * programma (numeri troppo grandi, un segno che non si riesce a stabilire)
 * l'errore resta annotato e la risposta non vuol dire nulla: chi chiama lo
 * deve guardare. */
static int sign_holds_at(const Formula *f, int name, Frac value) {
    /* Un errore già annotato va lasciato dov'è. Prima ogni confronto lo
     * azzerava: se il primo membro di un "se e solo se" usciva dai limiti e
     * il secondo no, l'errore spariva e la riga, invece che non controllata,
     * risultava in disaccordo con la tabella. */
    if (failure) return 0;
    switch (f->kind) {
    case F_AND:     return sign_holds_at(f->a, name, value) && sign_holds_at(f->b, name, value);
    case F_OR:      return sign_holds_at(f->a, name, value) || sign_holds_at(f->b, name, value);
    case F_IMPLIES: return !sign_holds_at(f->a, name, value) || sign_holds_at(f->b, name, value);
    case F_IFF:     return sign_holds_at(f->a, name, value) == sign_holds_at(f->b, name, value);
    case F_NOT:     return !sign_holds_at(f->a, name, value);
    default:        break;
    }
    /* Prima con gli intervalli (capitolo 24), che dicono due cose certe:
     * se un membro lì non ha un valore, e allora il confronto non vale; e
     * se tutti e due ce l'hanno. */
    int nowhere = 0, side = 0;
    Range point = range_ratio(value.num, value.den);
    Range left = node_range(f->left, name, point, &nowhere), right = node_range(f->right, name, point, &nowhere);
    if (nowhere) return 0;
    int certain = range_known(left) && range_known(right);

    /* Poi il conto esatto, che riconosce l'uguaglianza. Con i soli numeri
     * razionali e le loro radici dice da sé quando un'espressione non è
     * definita. Con logaritmi e potenze no: annota le condizioni invece di
     * controllarle. Gli si crede se gli intervalli hanno già stabilito che i
     * due membri hanno un valore, oppure se le condizioni annotate, che sono
     * numeri, risultano tutte vere (conditions_hold()). */
    Scratch mark = scratch_mark();
    undefined = 0;
    env_count = 0;
    env_push(name, rat_frac(value));
    condition_count = conditions_lost = 0;
    conditions_on = 1;
    Rat d = rat_add(eval(f->left), eval(f->right), 1);
    conditions_on = 0;
    env_count = 0;
    int absent = failure && undefined, broken = 0;
    int trusted = !failure && !conditions_lost && (certain || conditions_hold(&broken));
    int known = trusted && number_sign(d, &side);
    scratch_drop(mark);
    if (absent || broken) { failure = NULL; return 0; }

    /* Se il conto esatto non decide, il segno certo della differenza; e due
     * membri scritti allo stesso modo, che hanno un valore, sono uguali. Se
     * nemmeno così si decide resta un errore, che chi chiama controlla. */
    if (!known) {
        failure = NULL;
        if (certain && range_side(range_sub(left, right), &side)) known = 1;
        else if (certain && node_equal(f->left, f->right)) known = 1, side = 0;
        else fail("non riesco a stabilire il segno di un numero dell'enunciato");
    }
    if (!known) return 0;
    return f->kind == F_EQUAL ? side == 0 : f->kind == F_DISTINCT ? side != 0 : f->kind == F_LESS ? side < 0 : side <= 0;
}

/* Ritorna 1 se i due membri del confronto f sono la stessa funzione: se la
 * loro differenza, calcolata con la variabile come lettera e con il conto
 * esatto del motore (per seni e coseni le formule di Eulero, capitolo 11), è
 * zero per il test di annullamento del capitolo 12. Un "sì" è una
 * dimostrazione dell'identità, fatta per una strada che non passa dalla
 * tabella dei segni: per questo vale come suo controllo. Il risultato si
 * ricorda nel confronto preparato, se c'è. */
static int formula_identity(const Formula *f) {
    SignAtom *atom = NULL;
    for (int i = 0; i < sign_atoms; i++)
        if (sign_atom[i].source == f) atom = &sign_atom[i];
    if (atom && atom->identity) return atom->identity > 0;
    Scratch mark = scratch_mark();
    const char *was = failure;
    int live = trig_live, listed = conditions_on, bound = env_count;
    failure = NULL;
    trig_live = conditions_on = env_count = 0;
    Rat gap = rat_add(eval(f->left), eval(f->right), 1);
    int same = !failure && (gap.num.count == 0 || poly_vanishes(gap.num));
    failure = was;
    trig_live = live;
    conditions_on = listed;
    env_count = bound;
    scratch_drop(mark);
    if (atom) atom->identity = same ? 1 : -1;
    return same;
}

/* Ciò che serve a provare con i numeri le famiglie di un quantificatore su
 * un intero: la variabile, il suo valore, se un'uguaglianza quasi certa si
 * può prendere per buona, e il risultato che si accumula: 1 se la variabile
 * sta di sicuro in una famiglia, -1 se di una non si sa, 0 altrimenti. */
typedef struct {
    int name;
    Range x;
    int tolerant;
    int seen;
} FamilyCheck;

/* Ritorna la distanza di v dall'intero più vicino, come intervallo. */
static Range range_from_integer(Range v) {
    double middle = (v.low + v.high) / 2, nearest = (double)(long long)(middle + (middle < 0 ? -0.5 : 0.5));
    return range_known(v) && middle < 1e15 && middle > -1e15 ? range_sub(v, (Range){nearest, nearest}) : range_none();
}

/* Per range_truth: prova con i numeri se la variabile sta nella famiglia
 * del pezzo d, e aggiorna il risultato in context (un FamilyCheck). Il
 * periodo T e gli estremi per k = 0 si calcolano dalle espressioni; poi si
 * cerca il k giusto tra i tre più vicini a (x - low) / T. */
static void family_range(const Formula *owner, const Formula *d, void *context) {
    FamilyCheck *check = context;
    Family family;
    Range zero = {0, 0}, one = {1, 1};
    int none = 0, side = 0, found = 0;
    if (check->seen == 1) return;
    if (!family_read(d, check->name, owner->variable, owner->kind == F_FORALL, &family)) { check->seen = -1; return; }
    Range low = node_range(family.low, family.k, zero, &none), period = range_sub(node_range(family.low, family.k, one, &none), low);
    if (!range_side(period, &side)) { check->seen = -1; return; }
    if (side < 0) period = range_neg(period);
    Range turns = range_div(range_sub(check->x, low), period);
    if (!range_known(turns)) { check->seen = -1; return; }

    /* Un punto per ogni k: (x - low) / T deve essere un intero. */
    if (family.single) {
        Range gap = range_from_integer(turns);
        if (range_side(gap, &side)) return;
        check->seen = check->tolerant && range_known(gap) && gap.high - gap.low < 1e-6 ? 1 : -1;
        return;
    }

    /* Un intervallo per ogni k. */
    Range high = node_range(family.high, family.k, zero, &none);
    double middle = (turns.low + turns.high) / 2, base = (double)(long long)middle - (middle < 0);
    for (int step = -1; step <= 1 && !found; step++) {
        Range shift = range_mul((Range){base + step, base + step}, period);
        Range left = range_sub(check->x, range_add(low, shift)), right = range_sub(range_add(high, shift), check->x);
        int left_side = 0, right_side = 0, left_known = range_side(left, &left_side), right_known = range_side(right, &right_side);
        if ((left_known && left_side < 0) || (right_known && right_side < 0)) continue;
        if (!range_known(left) || !range_known(right)) { check->seen = -1; return; }

        /* Dentro, oppure su un estremo: lì conta se l'estremo è compreso, e
         * lo si può dire solo se è permesso prendere per zero una
         * differenza stretta attorno allo zero. */
        if ((!left_known || !right_known) && (!check->tolerant || left.high - left.low > 1e-6 || right.high - right.low > 1e-6)) { check->seen = -1; return; }

        /* Su un estremo escluso il valore non sta in questo intervallo, ma
         * può stare nel successivo: capita quando l'intervallo è lungo un
         * periodo intero, e l'estremo di uno è anche quello dell'altro. Una
         * versione che qui si fermava dava per escluso un punto compreso. */
        found = (left_known || family.low_closed) && (right_known || family.high_closed);
    }
    if (!found) return;

    /* I punti tolti: x - hole non deve essere un multiplo di T, per i punti
     * tolti che stanno nell'intervallo dello stesso k. */
    for (int h = 0; h < family.holes; h++) {
        Range hole = node_range(family.hole[h], family.k, zero, &none);
        int after = range_side(range_sub(hole, low), &side) ? side : 0, before = range_side(range_sub(high, hole), &side) ? side : 0;
        if (after == 0 || before == 0) { check->seen = -1; return; }
        if (after < 0 || before < 0) continue;
        Range gap = range_from_integer(range_div(range_sub(check->x, hole), period));
        if (range_side(gap, &side)) continue;
        if (!check->tolerant || !range_known(gap) || gap.high - gap.low > 1e-6) { check->seen = -1; return; }
        return;
    }
    check->seen = 1;
}

/* La logica a tre valori di Kleene, con 1 vero, 0 falso e -1 "non si sa":
 * ritorna il valore del connettivo kind (F_NOT, F_AND, F_OR, F_IMPLIES o
 * F_IFF) sulle parti a e b, e b non conta per F_NOT. Un "non so" pesa solo
 * dove potrebbe cambiare il risultato: "falso e non so" è falso, "vero o
 * non so" è vero, "vero e non so" è non so. L'implicazione è "non a, oppure
 * b"; l'equivalenza si sa solo se si sanno tutte e due le parti. È la logica
 * giusta per un conto che a volte non sa rispondere: ciò che dice di sicuro
 * resta sicuro, qualunque sia la risposta che manca. */
static int truth_join(FormulaKind kind, int a, int b) {
    if (kind == F_NOT) return a < 0 ? -1 : !a;
    if (kind == F_IMPLIES && a >= 0) a = !a;
    if (kind == F_AND) return a == 0 || b == 0 ? 0 : a < 0 || b < 0 ? -1 : 1;
    if (kind == F_IFF) return a < 0 || b < 0 ? -1 : a == b;
    return a == 1 || b == 1 ? 1 : a < 0 || b < 0 ? -1 : 0;
}

/* Ritorna 1 se la condizione f, senza quantificatori, vale di sicuro quando
 * la variabile name sta nell'intervallo x, 0 se di sicuro non vale, -1 se
 * gli intervalli non bastano a dirlo (capitolo 24). I connettivi seguono la
 * logica a tre valori (truth_join()): "falso e non so" è falso, "vero e non
 * so" è non so.
 *
 * Un confronto è falso di sicuro dove un suo membro di sicuro non ha un
 * valore; è deciso quando la differenza dei membri ha un segno certo. Se la
 * differenza contiene lo zero di solito non si sa. Con tolerant diverso da
 * zero, e una differenza stretta attorno allo zero, la si prende per zero:
 * serve nei punti in cui la tabella afferma un'uguaglianza, che con gli
 * intervalli si può trovare compatibile ma non dimostrare. */
static int range_truth(const Formula *f, int name, Range x, int tolerant) {
    int nowhere = 0, side = 0;
    if (family_owner(f)) {
        FamilyCheck check = {name, x, tolerant, 0};
        family_each(f, f->a, family_range, &check);
        return check.seen < 0 ? -1 : f->kind == F_EXISTS ? check.seen : !check.seen;
    }
    if (f->kind == F_AND || f->kind == F_OR || f->kind == F_IMPLIES || f->kind == F_IFF || f->kind == F_NOT) {
        int a = range_truth(f->a, name, x, tolerant), b = f->kind == F_NOT ? -1 : range_truth(f->b, name, x, tolerant);
        return truth_join(f->kind, a, b);
    }
    Range left = node_range(f->left, name, x, &nowhere), right = node_range(f->right, name, x, &nowhere), gap = range_sub(left, right);
    if (nowhere) return 0;
    if (!range_known(gap)) return -1;

    /* Una differenza che contiene lo zero: è zero di sicuro se i due membri
     * sono la stessa funzione, cosa che per le identità goniometriche il
     * conto esatto con le formule di Eulero sa riconoscere
     * (formula_identity()); altrimenti la si prende per zero solo se è
     * permesso, ed è stretta. */
    if (!range_side(gap, &side) && !formula_identity(f) && (!tolerant || gap.high - gap.low > 1e-6)) return -1;
    return f->kind == F_EQUAL ? side == 0 : f->kind == F_DISTINCT ? side != 0 : f->kind == F_LESS ? side < 0 : side <= 0;
}

/* Il controllo indipendente della tabella in un valore della sua lettera:
 * ritorna 1 se il conto con i numeri dà per la condizione body la stessa
 * verità truth della tabella, 0 se ne dà una diversa, -1 se non riesce a
 * dirlo. Il valore è il razionale at; oppure, se point non è NULL, il punto
 * point, che può non essere razionale.
 *
 * Tre casi. In un enunciato periodico la lettera è t, e la variabile vale
 * (2 / g) arctan t: un numero non razionale, che si conosce con un
 * intervallo. Un punto non razionale si conosce anche lui con un
 * intervallo. Negli altri casi il valore si sostituisce esattamente
 * (sign_holds_at()). */
static int table_agrees(const Formula *body, int name, Wide at, const Critical *point, int truth) {
    if (!trig_on && !point) {
        if (at.num >= COEF_LIMIT || at.num <= -COEF_LIMIT || at.den >= COEF_LIMIT) return -1;
        failure = NULL;
        int direct = sign_holds_at(body, name, (Frac){(long long)at.num, (long long)at.den});
        int known = failure == NULL;
        failure = NULL;
        return known ? direct == truth : -1;
    }
    Range value = range_ratio(at.num, at.den);
    if (point && point->kappa >= 0) value = kappa[point->kappa].value;
    else if (point && !point->exact) value = root_range(&sign_base[point->element], point->low, point->high);
    /* In un enunciato periodico il valore della variabile nel giro in corso:
     * (2 arctan t + 2 pi j) / g. */
    if (trig_on) value = range_div(range_add(range_mul(range_ratio(2, 1), range_atan(value)), range_mul(range_ratio(2 * window_turn, 1), range_pi())), range_ratio(trig_scale.num, trig_scale.den));
    /* In un enunciato periodico un'identità che il conto esatto non
     * riconosce (formula_identity()) si può solo trovare compatibile: lì la
     * conferma è una verifica con i numeri, non una seconda dimostrazione. */
    int seen = range_truth(body, name, value, point != NULL || trig_on);
    return seen < 0 ? -1 : seen == truth;
}

/* =============================================================================
 * 18.13 LE RIGHE DELLA TABELLA E LE SOLUZIONI
 * ============================================================================
 *
 * Con i punti in ordine (18.8) e i confronti preparati (18.11), la tabella:
 * una riga per ogni punto e per ogni intervallo tra due punti, con i segni
 * di tutti i polinomi in un valore della riga, ricontrollata con i numeri
 * (18.12) prima di essere creduta (sign_table()). Poi ciò che se ne legge e
 * si scrive: le righe nella dimostrazione (put_row()), e le soluzioni di una
 * condizione, i tratti di righe consecutive in cui vale (sign_solution()),
 * rilette dal testo prima di essere consegnate (solution_reread()).
 */

/* Le righe della tabella appena riempita da sign_table(): valgono fino alla
 * tabella successiva, e le leggono la dimostrazione, le soluzioni, il
 * grafico, il certificato e lo studio di funzione (capitolo 27). */
SignRow sign_row[2 * MAX_POINTS + 1];
int sign_rows;

/* Mette in out[], che ha 8 posti, altri valori della riga row, che è un
 * intervallo, oltre a quello scelto in sign_row[row].sample; ritorna quanti.
 *
 * Un punto solo conferma che la riga è giusta lì, non che l'intervallo sia
 * tutto di un segno: se alla tabella mancasse un punto, perché una regola ha
 * dato per costante un segno che non lo è, nel punto scelto potrebbe non
 * vedersi. È successo con x + 2^x, dato per positivo ovunque e confermato in
 * x = 0. Per questo chi ricontrolla una riga la prova anche in due punti tra
 * il valore scelto e ogni estremo, e dalla parte in cui l'estremo non c'è
 * in quattro punti via via più lontani. */
static int row_points(int row, Wide *out) {
    static const long long reach[4] = {1, 3, 10, 40};
    const Critical *before = row >= 2 ? &sign_point[row / 2 - 1] : NULL, *after = row / 2 < sign_points_count ? &sign_point[row / 2] : NULL;
    Wide sample = sign_row[row].sample;
    int count = 0;
    for (int side = 0; side < 2; side++) {
        const Critical *end = side ? after : before;
        if (end) {
            Wide edge = side ? end->low : end->high, near = side ? wide_between(sample, edge) : wide_between(edge, sample);
            out[count++] = near;
            out[count++] = side ? wide_between(near, edge) : wide_between(edge, near);
        } else {
            for (int i = 0; i < 4; i++) out[count++] = wide_add(sample, (Wide){side ? reach[i] : -reach[i], 1});
        }
    }
    if (failure) { failure = NULL; return 0; }
    return count;
}

/* Ritorna il razionale in cui si calcola una riga che è un intervallo, tra
 * i punti before e after che la chiudono (NULL se da quella parte non c'è un
 * punto): un razionale semplice tra i due (wide_between()), oppure l'intero
 * che sta due unità oltre l'unico punto che c'è, oppure 0 se non ce n'è
 * nessuno. Lo stesso valore sceglie la regola 18t per le celle della retta
 * del parametro, che sono righe di una tabella nella sua lettera. */
static Wide interval_sample(const Critical *before, const Critical *after) {
    if (before && after) return wide_between(before->high, after->low);
    if (after) return (Wide){after->low.num / after->low.den - 2, 1};
    if (before) return (Wide){before->high.num / before->high.den + 2, 1};
    return (Wide){0, 1};
}

/* Mette tra le colonne della tabella i polinomi x - a che delimitano set,
 * cioè il suo estremo inferiore e i suoi punti tolti, e ritorna il posto in
 * sign_poly[] del primo (-1 se set non ha un estremo); i posti dei punti
 * tolti vanno in hole_column[]. Una colonna che c'è già si ritrova
 * (sign_column()): così il certificato (18p-15) usa le colonne della tabella
 * che ha deciso. */
static int set_columns(const NumberSet *set, int *hole_column) {
    int floor_column = set->bounded ? sign_column((Uni){1, {-(__int128)set->low, 1}}) : -1;
    for (int i = 0; i < set->holes; i++) hole_column[i] = sign_column((Uni){1, {-(__int128)set->hole[i].num, set->hole[i].den}});
    return floor_column;
}

/* Ritorna 1 se i segni sign[] di una riga dicono che la riga non sta sotto
 * l'estremo inferiore di set, né su un suo punto tolto: le colonne di quei
 * polinomi sono quelle di set_columns(). */
static int row_in_set(const int *sign, const NumberSet *set, int floor_column, const int *hole_column) {
    if (floor_column >= 0 && (sign[floor_column] < 0 || (sign[floor_column] == 0 && set->strict))) return 0;
    for (int i = 0; i < set->holes; i++)
        if (sign[hole_column[i]] == 0) return 0;
    return 1;
}

/* 18p-2. Riempie sign_row[]: per ogni riga il valore, i segni dei polinomi,
 * se sta in set, e l'esito del controllo indipendente della condizione body
 * nella variabile name. floor_column e hole_column[] sono i posti, in
 * sign_poly[], dei polinomi x - a che delimitano set: il suo estremo
 * inferiore (-1 se non c'è) e i punti tolti.
 *
 * Il controllo indipendente si fa dove il valore è un razionale: lo si
 * sostituisce nell'enunciato e si fa il conto con i numeri. Se il conto esce
 * dai limiti la riga resta non confermata. Un intervallo viene poi provato
 * in altri punti, per accorgersi di un punto che alla tabella mancasse.
 * Nelle radici irrazionali il controllo non si può fare: lì la tabella
 * poggia solo su 18p-5.
 *
 * Ritorna 0 se in una riga il conto con i numeri smentisce la tabella: è un
 * errore del programma, e nessuna riga va più creduta. */
static int sign_table(const Formula *body, int name, const NumberSet *set, int floor_column, const int *hole_column) {
    int sound = 1;
    sign_rows = 2 * sign_points_count + 1;
    for (int row = 0; row < sign_rows && !failure; row++) {
        SignRow *r = &sign_row[row];
        const Critical *point = row % 2 ? &sign_point[row / 2] : NULL;
        const Critical *before = row >= 2 ? &sign_point[row / 2 - 1] : NULL, *after = row / 2 < sign_points_count ? &sign_point[row / 2] : NULL;

        /* Il valore in cui si calcolano i segni. */
        r->sample = !point ? interval_sample(before, after) : point->exact ? point->low : wide_mid(point->low, point->high);
        r->rational = !point || point->exact;
        for (int i = 0; i < sign_polys && !failure; i++) {
            Uni rest;
            if (sign_kappa[i] >= 0) {
                /* x - k: dipende solo da dove sta la riga rispetto al punto k. */
                int place = 0;
                while (sign_point[place].kappa != sign_kappa[i]) place++;
                r->sign[i] = (row > 2 * place + 1) - (row < 2 * place + 1);
            } else if (sign_space[i] >= 0) {
                r->sign[i] = 0;  /* un polinomio in un'altra lettera: non è un segno di questa tabella */
            } else {
                r->sign[i] = (!r->rational && point->element >= 0 && uni_divide(&sign_poly[i], &sign_base[point->element], &rest)) ? 0 : uni_sign_at(&sign_poly[i], r->sample);
            }
        }
        if (failure) break;

        /* La riga conta solo se sta nell'insieme su cui varia la variabile:
         * tra i razionali, solo un punto razionale o un intervallo. */
        r->inside = (set->reals || r->rational) && row_in_set(r->sign, set, floor_column, hole_column);

        /* Il controllo indipendente (table_agrees()). Una riga con un
         * valore razionale si rifà con il conto esatto, e deve riuscire. Una
         * radice irrazionale, e ogni riga di un enunciato periodico, si
         * rifà con gli intervalli: lì un'uguaglianza si può solo trovare
         * compatibile, non dimostrare, ma un segno sbagliato si vede. */
        int exact = r->rational && !trig_on;
        r->confirmed = 0;
        r->must = trig_on ? !point : r->rational;
        if (!r->inside) continue;

        /* Con le finestre (18p-14) la riga dice una cosa diversa in ogni
         * giro, e si ricontrolla in ognuno; altrimenti il giro è uno solo. */
        Wide more[8];
        int count = point ? 0 : row_points(row, more), every = 1;
        for (window_turn = window_first; window_turn <= window_last && sound; window_turn++) {
            int truth = sign_truth(body, r->sign), agreed = table_agrees(body, name, r->sample, exact ? NULL : point, truth);
            if (agreed == 0) sound = 0;
            if (agreed != 1) every = 0;

            /* Un intervallo si ricontrolla anche in altri punti (row_points()). */
            for (int extra = 0; extra < count && sound; extra++)
                if (table_agrees(body, name, more[extra], NULL, truth) == 0) sound = 0;
        }
        window_turn = 0;
        r->confirmed = every;
    }
    return sound;
}

/* Scrive nella dimostrazione il punto numero k della tabella: il razionale,
 * il numero con il suo logaritmo, oppure, per una radice non razionale, il
 * nome r con il suo posto tra i punti, lo stesso che ha nella sua riga. */
static void put_point(int k) {
    const Critical *point = &sign_point[k];
    if (point->kappa >= 0) proof_add("%s", kappa[point->kappa].text);
    else if (point->exact) put_wide(point->low);
    else proof_add("r_{%d}", k + 1);
}

/* Scrive nella dimostrazione di quale riga della tabella si parla: il punto,
 * la radice con l'intervallo che la isola, o l'intervallo con il valore
 * scelto al suo interno. name è la variabile. */
static void put_row(int row, int name) {
    const Critical *point = row % 2 ? &sign_point[row / 2] : NULL;
    if (point && point->element >= 0) {
        proof_add("$%c = r_{%d}$, the root of $", name, row / 2 + 1);
        put_uni(&sign_base[point->element], name);
        proof_add("$ between $");
        put_wide(point->low);
        proof_add("$ and $");
        put_wide(point->high);
        proof_add("$");
        return;
    }
    if (point) { proof_add("$%c = ", name); put_point(row / 2); proof_add("$"); return; }

    /* Un intervallo: i due punti che lo chiudono, se ci sono, e il valore
     * scelto al suo interno. */
    proof_add("$");
    if (row >= 2) { put_point(row / 2 - 1); proof_add(" < "); }
    proof_add("%c", name);
    if (row / 2 < sign_points_count) { proof_add(" < "); put_point(row / 2); }
    proof_add("$ (for instance $%c = ", name);
    put_wide(sign_row[row].sample);
    proof_add("$)");
}

/* Le soluzioni trovate da sign_solution(), come condizione in LaTeX, e ciò
 * che va detto per leggerle: se hanno estremi irrazionali, e che cosa
 * indicano i nomi r_{k}. Valgono fino alla tabella successiva. */
char solution_text[1024], solution_note[512];

/* Ritorna 1 se il punto numero k della tabella, una radice irrazionale, è il
 * primo dei punti che sono radici del suo elemento della base: per un
 * elemento di secondo grado, la più piccola delle due radici, perché i punti
 * sono in ordine. */
int point_is_first_root(int k) {
    for (int i = 0; i < k; i++)
        if (!sign_point[i].exact && sign_point[i].element == sign_point[k].element) return 0;
    return 1;
}

/* Aggiunge a text, di size byte, il punto numero k della tabella, scritto
 * come estremo di una soluzione: un razionale, oppure una radice.
 *
 * Una radice irrazionale ha una scrittura con i radicali quando l'elemento
 * della base che la annulla ha grado 2 (quadratic_latex()). Negli altri
 * casi la radice prende il nome r_{k+1}, quello che ha nella dimostrazione, e
 * solution_note dice quale numero è. */
static void point_latex(int k, int name, char *text, size_t size) {
    const Critical *point = &sign_point[k];
    if (point->kappa >= 0) { text_add(text, size, "%s", kappa[point->kappa].text); return; }
    if (point->exact) { wide_latex(point->low, text, size); return; }

    /* La più piccola delle due radici è il primo dei due punti di questo
     * elemento. */
    const Uni *q = &sign_base[point->element];
    if (quadratic_latex(q, point_is_first_root(k), text, size)) return;

    /* Una radice senza scrittura: il nome, e nella nota di quale numero si
     * tratta, una volta sola. */
    char label[24], low[48], high[48];
    snprintf(label, sizeof label, "r_{%d}", k + 1);
    text_add(text, size, "%s", label);
    if (strstr(solution_note, label)) return;
    wide_text(point->low, low, sizeof low);
    wide_text(point->high, high, sizeof high);
    text_add(solution_note, sizeof solution_note, "; %s è la radice di ", label);
    uni_latex(q, name, solution_note, sizeof solution_note);
    text_add(solution_note, sizeof solution_note, " tra %s e %s", low, high);
}

/* Cerca il primo pezzo, dalla riga from in poi, in cui vale la condizione f
 * secondo le righe di sign_row[]. Ritorna 0 se non ce ne sono più.
 *
 * Un pezzo che comincia su una riga dispari, cioè su un punto, comprende
 * quel punto; se comincia su un intervallo, il punto che lo precede resta
 * fuori. Lo stesso alla fine. */
int sign_piece(const Formula *f, int from, Piece *piece) {
    int first = from;
    while (first < sign_rows && !(sign_row[first].inside && sign_truth(f, sign_row[first].sign))) first++;
    if (first >= sign_rows) return 0;
    int last = first;
    while (last + 1 < sign_rows && sign_row[last + 1].inside && sign_truth(f, sign_row[last + 1].sign)) last++;
    *piece = (Piece){first, last, first == 0 ? -1 : first % 2 ? first / 2 : first / 2 - 1, last == sign_rows - 1 ? -1 : last / 2, first % 2, last % 2};
    return 1;
}

/* Scrive in solution_text i valori della variabile name per cui vale la
 * condizione f, secondo le righe di sign_row[]: una condizione in LaTeX
 * com'è scritta nei libri, per esempio x < -3 \lor x \ge 2, con un pezzo
 * per ogni intervallo o punto (sign_piece()).
 *
 * Ritorna 1 se il testo si può rileggere e ricontrollare; 0 se usa un nome
 * per una radice che non ha una scrittura, o se è una delle due frasi senza
 * estremi ("nessun x", "ogni x"). */
static int sign_solution(const Formula *f, int name) {
    int pieces = 0, plain = 1;
    Piece piece;
    solution_text[0] = solution_note[0] = '\0';
    for (int from = 0; !failure && sign_piece(f, from, &piece); from = piece.last + 1) {
        int low = piece.low, high = piece.high, low_closed = piece.low_closed, high_closed = piece.high_closed;
        if (pieces++) text_add(solution_text, sizeof solution_text, " \\lor ");
        if (low < 0 && high < 0) {
            text_add(solution_text, sizeof solution_text, "\\forall %c \\in \\mathbb{R}", name);
            plain = 0;
        } else if (piece.first == piece.last && low_closed) {
            text_add(solution_text, sizeof solution_text, "%c = ", name);
            point_latex(low, name, solution_text, sizeof solution_text);
        } else if (low < 0 || high < 0) {
            text_add(solution_text, sizeof solution_text, "%c %s ", name, low < 0 ? (high_closed ? "\\le" : "<") : (low_closed ? "\\ge" : ">"));
            point_latex(low < 0 ? high : low, name, solution_text, sizeof solution_text);
        } else {
            point_latex(low, name, solution_text, sizeof solution_text);
            text_add(solution_text, sizeof solution_text, " %s %c %s ", low_closed ? "\\le" : "<", name, high_closed ? "\\le" : "<");
            point_latex(high, name, solution_text, sizeof solution_text);
        }
    }
    if (!pieces) {
        text_add(solution_text, sizeof solution_text, "\\nexists %c \\in \\mathbb{R}", name);
        plain = 0;
    }
    return plain && !solution_note[0];
}

/* Rilegge come una condizione, con il lettore degli enunciati (capitolo 17),
 * il testo text che il programma ha appena scritto. Ritorna l'albero, oppure
 * NULL se il testo non si rilegge tutto: un errore di sintassi, o qualcosa
 * dopo la condizione. In ogni caso syntax_error resta NULL. È il primo passo
 * di ogni controllo di ciò che si consegna (18p, 18t-f): il controllo
 * guarda ciò che il testo dice, non ciò che il motore pensava di scrivere. */
Formula *condition_reread(const char *text) {
    syntax_error = NULL;
    cursor = text;
    next_token();
    Formula *written = logic_formula();
    if (syntax_error || token.kind != T_END) { syntax_error = NULL; return NULL; }
    return written;
}

/* Rilegge le soluzioni scritte in solution_text e controlla che dicano ciò
 * che dice la tabella: in ogni riga razionale la condizione riletta, con il
 * valore della riga al posto della variabile name, deve valere esattamente
 * quando vale f. È il controllo di ciò che si consegna, cioè del testo: un
 * < scritto al posto di un \le, o un estremo con il segno sbagliato, qui si
 * vede. Ritorna 1 se tutte le righe concordano. */
static int solution_reread(const Formula *f, int name) {
    const Formula *written = condition_reread(solution_text);
    if (!written) return 0;
    for (int row = 0; row < sign_rows; row++) {
        const SignRow *r = &sign_row[row];
        Wide at[9];
        if (!r->inside || !r->rational) continue;

        /* Il valore della riga, che deve riuscire; e per un intervallo gli
         * altri suoi punti, dove un estremo scritto male si vede anche se
         * il valore scelto sta dalla parte giusta di tutti e due. */
        int count = row % 2 ? 0 : row_points(row, at + 1);
        at[0] = r->sample;
        for (int i = 0; i <= count; i++) {
            if (at[i].num >= COEF_LIMIT || at[i].num <= -COEF_LIMIT || at[i].den >= COEF_LIMIT) { if (i == 0) return 0; continue; }
            failure = NULL;
            int direct = sign_holds_at(written, name, (Frac){(long long)at[i].num, (long long)at[i].den});
            if (failure && i > 0) { failure = NULL; continue; }
            if (failure || direct != sign_truth(f, r->sign)) { failure = NULL; return 0; }
        }
    }
    return 1;
}

/* =============================================================================
 * 18.14 LE SOLUZIONI DI UNA CONDIZIONE PERIODICA (18p-12, 18p-14)
 * ============================================================================
 *
 * La tabella di un enunciato periodico è nella lettera t = tan(u / 2), con
 * u = g x. Per scrivere le soluzioni in x bisogna tornare indietro:
 *
 *   - un punto t_0 della tabella è l'angolo u_0 = 2 arctan t_0, tra -pi e
 *     pi; un tratto di righe consecutive in cui la condizione vale è un
 *     arco della circonferenza; il punto u = pi, calcolato a parte, chiude
 *     il giro e può unire l'ultimo arco al primo;
 *   - le soluzioni in u si ripetono ogni 2 pi, quindi in x ogni 2 pi / g; ma
 *     l'insieme può avere un periodo più piccolo (le soluzioni di
 *     tan x = 1 si ripetono ogni pi), e si cerca il più piccolo tra i
 *     sottomultipli;
 *   - gli estremi si scrivono, quando si può, come multipli razionali di
 *     pi. Che u_0 sia proprio p pi / q, e non un numero vicino, si
 *     stabilisce con un conto esatto: vedi angle_of_point().
 */

/* Un angolo, in giri di pi: vale turns * pi più una parte fissa che dipende
 * da kind. Due angoli dello stesso tipo, con la stessa parte fissa, sono
 * uguali quando hanno lo stesso turns: è così che gli angoli si confrontano
 * senza errori. near è il suo valore approssimato diviso pi, che serve solo
 * a metterli in ordine. */
typedef struct {
    int kind;      /* 0: nessuna parte fissa, l'angolo è un multiplo razionale di
                      pi; 1: la parte fissa è arctan(slope); 2: è
                      2 arctan(t), con t il punto numero point della tabella */
    Frac turns;    /* il multiplo razionale di pi che si aggiunge alla parte fissa */
    Frac slope;    /* kind 1 */
    int point;     /* kind 2 */
    double near;   /* il valore approssimato diviso pi: solo per l'ordine */
} Angle;

/* Un arco dell'insieme delle soluzioni, da from a to nel verso in cui gli
 * angoli crescono; un punto solo se single. period è ogni quanto si ripete,
 * in giri di pi di u: lo usa solo la scrittura delle famiglie (18p-12). */
typedef struct {
    Angle from, to;
    int from_closed, to_closed, single;
    Frac period;
} Arc;

/* Ritorna il polinomio S_q(t), la parte immaginaria di (1 + i t)^q: la somma
 * sui j dispari di (-1)^((j-1)/2) C(q, j) t^j. */
static Uni half_angle_poly(int q) {
    Uni p = {0, {0}};
    __int128 binomial = 1;
    for (int j = 0; j <= q; j++) {
        if (j % 2) p.c[j] = (j / 2) % 2 ? -binomial : binomial;
        binomial = binomial * (q - j) / (j + 1);
    }
    p.degree = q;
    uni_trim(&p);
    return p;
}

/* Ritorna l'angolo u_0 = 2 arctan t_0 del punto numero k della tabella.
 *
 * Quando u_0 è un multiplo razionale di pi lo si riconosce così. Il numero
 * 1 + i t_0 ha per argomento arctan t_0 = u_0 / 2; quindi (1 + i t_0)^q ha
 * per argomento q u_0 / 2, ed è un numero reale esattamente quando q u_0 è
 * un multiplo di 2 pi, cioè quando la sua parte immaginaria S_q(t_0) è
 * zero. Che t_0 annulli S_q è un fatto esatto: per un razionale è un conto;
 * per una radice irrazionale di un elemento e della base, vuol dire che il
 * massimo comun divisore di e e di S_q ha una radice nell'intervallo che
 * isola t_0, e le radici in un intervallo le conta il teorema di Sturm.
 * Saputo che q u_0 è un multiplo di 2 pi, quale multiplo lo dice il valore
 * approssimato, perché i multipli distano 2 pi / q l'uno dall'altro. Si
 * provano i q dei libri, dai più piccoli: con q = 12 si riconosce pi/6, con
 * 24 pi/12, con 16 pi/8, con 20 pi/10.
 *
 * Altrimenti, se tan u_0 = 2 t_0 / (1 - t_0^2) è un razionale m, l'angolo è
 * arctan m, più o meno pi. Lo è per un t_0 razionale, e per una radice di
 * a t^2 + b t - a, dove vale 2a / b perché a (1 - t^2) = b t. Negli altri
 * casi l'angolo resta scritto come 2 arctan t_0. */
static Angle angle_of_point(int k) {
    static const int tries[] = {1, 2, 3, 4, 6, 12, 8, 5, 10, 24, 16, 20};
    const Critical *point = &sign_point[k];
    Range value = point->exact ? range_ratio(point->low.num, point->low.den) : root_range(&sign_base[point->element], point->low, point->high);
    Range turn = range_div(range_mul(range_ratio(2, 1), range_atan(value)), range_pi());
    Angle angle = {2, frac_int(0), frac_int(0), k, (turn.low + turn.high) / 2};

    /* Un multiplo razionale di pi. */
    for (size_t i = 0; i < sizeof tries / sizeof *tries && !failure; i++) {
        int q = tries[i];
        /* q u_0 deve essere un multiplo di 2 pi: near q / 2 un intero. */
        double scaled = angle.near * q / 2, nearest = (double)(long long)(scaled + (scaled < 0 ? -0.5 : 0.5));
        if (scaled - nearest > 1e-9 || nearest - scaled > 1e-9) continue;
        Uni imaginary = half_angle_poly(q);
        int zero;
        if (point->exact) {
            zero = uni_sign_at(&imaginary, point->low) == 0;
        } else {
            Uni common = uni_gcd(sign_base[point->element], imaginary);
            zero = common.degree >= 1;
            if (zero) {
                sturm_build(&common);
                zero = sturm_changes(point->low) - sturm_changes(point->high) == 1;
            }
        }
        if (failure || !zero) continue;
        angle.kind = 0;
        angle.turns = frac_make(2 * (long long)nearest, q);
        return angle;
    }

    /* arctan di un razionale, più o meno pi. */
    Frac slope = frac_int(0);
    int rational = 0;
    if (point->exact && point->low.num < 1000000 && point->low.num > -1000000 && point->low.den < 1000000) {
        Frac t = {(long long)point->low.num, (long long)point->low.den}, below = frac_add(frac_int(1), frac_neg(frac_mul(t, t)));
        rational = below.num != 0;
        if (rational) slope = frac_div(frac_add(t, t), below);
    } else if (!point->exact) {
        const Uni *e = &sign_base[point->element];
        rational = e->degree == 2 && e->c[0] == -e->c[2] && e->c[1] != 0 && e->c[2] < 1000000 && e->c[2] > -1000000 && e->c[1] < 1000000 && e->c[1] > -1000000;
        if (rational) slope = frac_make(2 * e->c[2], e->c[1]);
    }
    if (rational && !failure) {
        Range base = range_div(range_atan(range_ratio(slope.num, slope.den)), range_pi());
        double shift = angle.near - (base.low + base.high) / 2;
        angle.kind = 1;
        angle.slope = slope;
        angle.turns = frac_int((long long)(shift + (shift < 0 ? -0.5 : 0.5)));
    }
    failure = NULL;
    return angle;
}

/* Ritorna l'angolo a ruotato di turns giri di pi. */
static Angle angle_turn(Angle a, Frac turns) {
    a.turns = frac_add(a.turns, turns);
    a.near += (double)turns.num / (double)turns.den;
    return a;
}

/* Ritorna 1 se a e b sono lo stesso angolo a meno di multipli di modulus
 * (in giri di pi: 2 per i giri interi). */
static int angle_same(Angle a, Angle b, Frac modulus) {
    Frac gap = frac_div(frac_add(a.turns, frac_neg(b.turns)), modulus);
    if (a.kind != b.kind || gap.den != 1) return 0;
    return a.kind == 0 || (a.kind == 1 ? frac_cmp(a.slope, b.slope) == 0 : a.point == b.point);
}

/* Ritorna 1 se gli archi a e b sono lo stesso arco a meno di multipli di
 * modulus. */
static int arc_same(const Arc *a, const Arc *b, Frac modulus) {
    Frac gap = frac_add(a->from.turns, frac_neg(b->from.turns));
    return a->single == b->single && a->from_closed == b->from_closed && a->to_closed == b->to_closed &&
           angle_same(a->from, b->from, modulus) && angle_same(a->to, angle_turn(b->to, gap), modulus) && frac_cmp(a->to.turns, frac_add(b->to.turns, gap)) == 0;
}

/* Riporta l'arco *arc, che si ripete ogni period giri di pi, alla sua copia
 * di riferimento, quella che scrivono i libri: comincia tra 0 e il periodo,
 * come \frac{7}{6}\pi + 2k\pi < x < \frac{11}{6}\pi + 2k\pi; ma un intervallo
 * che così scavalcherebbe la fine del periodo si scrive attorno allo zero,
 * -\frac{\pi}{6} + 2k\pi \le x \le \frac{\pi}{3} + 2k\pi, e un punto scritto
 * con un'arcotangente resta, quando il periodo lo permette, senza multipli
 * di pi accanto: x = \arctan 2 + k\pi. */
static void arc_home(Arc *arc, Frac period) {
    double length = (double)period.num / (double)period.den, from = arc->from.near;
    long long steps = (long long)(from / length);
    Frac whole = frac_div(arc->from.turns, period);
    if (from < 0) steps--;
    if (from - steps * length > length - 1e-9) steps++;
    if (from - steps * length < -1e-9) steps--;
    if (!arc->single && arc->to.near - steps * length > length + 1e-9) steps++;
    if (arc->single && arc->from.kind != 0 && whole.den == 1) steps = whole.num;
    Frac back = frac_mul(frac_int(-steps), period);
    arc->from = angle_turn(arc->from, back);
    arc->to = angle_turn(arc->to, back);
    arc->period = period;
}

/* Aggiunge a text, di size byte, l'angolo a diviso per g = trig_scale, cioè
 * il valore della variabile, più il multiplo del periodo period (in giri di
 * pi, già diviso per g) se with_period non è zero: \frac{\pi}{6} + 2k\pi. */
static void angle_latex(Angle a, Frac period, int with_period, char *text, size_t size) {
    Frac turns = frac_div(a.turns, trig_scale), factor = frac_div(frac_int(a.kind == 2 ? 2 : 1), trig_scale);
    int written = 0;

    /* La parte fissa: un'arcotangente, con il suo fattore. */
    if (a.kind != 0) {
        char inside[96] = "";
        Frac size_of = a.slope;
        int minus = a.kind == 1 && a.slope.num < 0;
        if (minus) size_of.num = -size_of.num;
        if (a.kind == 1) wide_latex((Wide){size_of.num, size_of.den}, inside, sizeof inside); else point_latex(a.point, 't', inside, sizeof inside);
        if (minus) text_add(text, size, "-");
        if (factor.den != 1) text_add(text, size, "\\frac{%lld}{%lld}", factor.num, factor.den);
        else if (factor.num != 1) text_add(text, size, "%lld", factor.num);
        if (a.kind == 1 && size_of.den == 1) text_add(text, size, "\\arctan %s", inside); else text_add(text, size, "\\arctan\\left(%s\\right)", inside);
        written = 1;
    }

    /* Il multiplo di pi. */
    if (turns.num != 0) {
        long long top = turns.num < 0 ? -turns.num : turns.num;
        text_add(text, size, "%s", written ? (turns.num < 0 ? " - " : " + ") : (turns.num < 0 ? "-" : ""));
        if (turns.den == 1 && top == 1) text_add(text, size, "\\pi");
        else if (turns.den == 1) text_add(text, size, "%lld\\pi", top);
        else if (top == 1) text_add(text, size, "\\frac{\\pi}{%lld}", turns.den);
        else text_add(text, size, "\\frac{%lld}{%lld}\\pi", top, turns.den);
        written = 1;
    }

    /* Il periodo. */
    if (with_period) {
        text_add(text, size, "%s", written ? " + " : "");
        if (period.den == 1 && period.num == 1) text_add(text, size, "k\\pi");
        else if (period.den == 1) text_add(text, size, "%lldk\\pi", period.num);
        else if (period.num == 1) text_add(text, size, "\\frac{k\\pi}{%lld}", period.den);
        else text_add(text, size, "\\frac{%lldk\\pi}{%lld}", period.num, period.den);
    } else if (!written) {
        text_add(text, size, "0");
    }
}

/* Gli archi delle soluzioni dell'enunciato periodico in corso, e il periodo
 * dell'insieme in giri di pi di u. Li riempie trig_solution(), che li riduce
 * a un periodo e dà a ognuno il periodo della sua famiglia; oppure
 * window_solution() (18p-14), con gli intervalli così come sono, senza
 * periodo. */
static Arc trig_arc[MAX_ARCS];
static int trig_arcs;
static Frac trig_period;

/* 18p-12. Scrive in solution_text le soluzioni, nella variabile name, della
 * condizione periodica f, dalle righe della tabella in t e dal valore
 * at_pi che la condizione ha nel punto u = pi; riempie trig_arc[].
 * Ritorna 0, dopo aver annotato un errore, se gli archi sono troppi. */
static int trig_solution(const Formula *f, int name, int at_pi) {
    static const int parts[] = {24, 12, 8, 6, 5, 4, 3, 2, 1};
    Piece piece;
    Angle start = {0, frac_int(-1), frac_int(0), 0, -1}, end = {0, frac_int(1), frac_int(0), 0, 1};
    int first = -1, last = -1, whole = 0;
    trig_arcs = 0;
    solution_text[0] = solution_note[0] = '\0';

    /* Gli archi in un giro di u, da -pi a pi. Il primo può cominciare in
     * -pi e l'ultimo finire in pi: sono lo stesso punto della
     * circonferenza. */
    for (int from = 0; !failure && sign_piece(f, from, &piece); from = piece.last + 1) {
        if (trig_arcs == MAX_ARCS - 1) { fail("troppi archi nelle soluzioni di una condizione periodica"); return 0; }
        Arc *arc = &trig_arc[trig_arcs];
        arc->single = piece.first == piece.last && piece.first % 2;
        arc->from = piece.low < 0 ? start : angle_of_point(piece.low);
        arc->to = piece.high < 0 ? end : angle_of_point(piece.high);
        arc->from_closed = piece.low >= 0 && piece.low_closed;
        arc->to_closed = piece.high >= 0 && piece.high_closed;
        if (piece.low < 0) first = trig_arcs;
        if (piece.high < 0) last = trig_arcs;
        if (piece.low < 0 && piece.high < 0) whole = 1;
        trig_arcs++;
    }
    if (failure) return 0;

    /* Il punto u = pi. Se la condizione lì vale: unisce l'ultimo arco al
     * primo, o chiude quello dei due che c'è, o è una soluzione isolata. Se
     * non vale, i due archi restano aperti da quella parte. */
    if (whole && at_pi) {
        text_add(solution_text, sizeof solution_text, "\\forall %c \\in \\mathbb{R}", name);
        trig_arcs = 1;
        trig_period = frac_int(2);
        trig_arc[0] = (Arc){start, end, 1, 1, 0, frac_int(2)};
        return 1;
    }
    if (at_pi && first >= 0 && last >= 0) {
        trig_arc[last].to = angle_turn(trig_arc[first].to, frac_int(2));
        trig_arc[last].to_closed = trig_arc[first].to_closed;
        trig_arc[first] = trig_arc[--trig_arcs];
    } else if (at_pi && last >= 0) {
        trig_arc[last].to_closed = 1;
    } else if (at_pi && first >= 0) {
        trig_arc[first].from_closed = 1;
    } else if (at_pi) {
        trig_arc[trig_arcs++] = (Arc){end, end, 1, 1, 1, frac_int(2)};
    }
    if (trig_arcs == 0) {
        text_add(solution_text, sizeof solution_text, "\\nexists %c \\in \\mathbb{R}", name);
        trig_period = frac_int(2);
        return 1;
    }

    /* Il periodo più piccolo: il più grande m per cui ruotando ogni arco di
     * 2 pi / m si ritrova un arco dell'insieme. Gli archi sono massimali e
     * staccati, quindi l'insieme ruotato coincide con l'insieme quando
     * coincidono gli archi. */
    int m = 1;
    for (size_t i = 0; i < sizeof parts / sizeof *parts && m == 1; i++) {
        int same = 1;
        for (int a = 0; a < trig_arcs && same; a++) {
            Arc turned = trig_arc[a];
            int found = 0;
            turned.from = angle_turn(turned.from, frac_make(2, parts[i]));
            turned.to = angle_turn(turned.to, frac_make(2, parts[i]));
            for (int b = 0; b < trig_arcs && !found; b++) found = arc_same(&turned, &trig_arc[b], frac_int(2));
            same = found;
        }
        if (same) m = parts[i];
    }
    trig_period = frac_make(2, m);

    /* Un arco per ogni classe: gli altri sono le sue copie ruotate di un
     * periodo. */
    int kept = 0;
    for (int a = 0; a < trig_arcs; a++) {
        Arc arc = trig_arc[a];
        int copy = 0;
        arc_home(&arc, trig_period);
        for (int b = 0; b < kept && !copy; b++) copy = arc_same(&arc, &trig_arc[b], trig_period);
        if (!copy) trig_arc[kept++] = arc;
    }
    trig_arcs = kept;

    /* Le famiglie. Dentro il periodo dell'insieme alcuni archi possono
     * ripetersi più spesso: le soluzioni di sin(4x) = sin(2x) sono
     * x = k pi/2 e x = pi/6 + k pi/3, e solo insieme hanno periodo pi. Per
     * ogni divisore r, dai più grandi, un arco che ruotato di 1/r, 2/r, ...
     * del periodo ritrova altri archi dell'insieme li rappresenta tutti,
     * con il periodo diviso per r. Ogni famiglia così scritta è fatta di
     * archi dell'insieme, e ogni arco finisce in una famiglia: l'insieme
     * non cambia, cambia solo come lo si scrive. */
    int state[MAX_ARCS] = {0};  /* 1: rappresenta una famiglia; 2: è in quella di un altro */
    for (size_t i = 0; i < sizeof parts / sizeof *parts && parts[i] > 1; i++) {
        Frac step = frac_div(trig_period, frac_int(parts[i]));
        for (int a = 0; a < trig_arcs; a++) {
            int member[24], found = !state[a];
            for (int j = 1; j < parts[i] && found; j++) {
                Arc turned = trig_arc[a];
                turned.from = angle_turn(turned.from, frac_mul(step, frac_int(j)));
                turned.to = angle_turn(turned.to, frac_mul(step, frac_int(j)));
                found = 0;
                for (int b = 0; b < trig_arcs && !found; b++)
                    if (b != a && !state[b] && arc_same(&turned, &trig_arc[b], trig_period)) { member[j] = b; found = 1; }
            }
            if (!found) continue;
            state[a] = 1;
            for (int j = 1; j < parts[i]; j++) state[member[j]] = 2;
            arc_home(&trig_arc[a], step);
        }
    }
    kept = 0;
    for (int a = 0; a < trig_arcs; a++)
        if (state[a] != 2) trig_arc[kept++] = trig_arc[a];
    trig_arcs = kept;

    /* In ordine, e scritti nella variabile: gli angoli divisi per g. */
    for (int a = 0; a < trig_arcs; a++)
        for (int b = a + 1; b < trig_arcs; b++)
            if (trig_arc[b].from.near < trig_arc[a].from.near) { Arc swap = trig_arc[a]; trig_arc[a] = trig_arc[b]; trig_arc[b] = swap; }
    for (int a = 0; a < trig_arcs && !failure; a++) {
        const Arc *arc = &trig_arc[a];
        Frac shown = frac_div(arc->period, trig_scale);
        if (a) text_add(solution_text, sizeof solution_text, " \\lor ");
        if (arc->single) {
            text_add(solution_text, sizeof solution_text, "%c = ", name);
            angle_latex(arc->from, shown, 1, solution_text, sizeof solution_text);
            continue;
        }
        angle_latex(arc->from, shown, 1, solution_text, sizeof solution_text);
        text_add(solution_text, sizeof solution_text, " %s %c %s ", arc->from_closed ? "\\le" : "<", name, arc->to_closed ? "\\le" : "<");
        angle_latex(arc->to, shown, 1, solution_text, sizeof solution_text);
    }
    return !failure;
}

/* 18p-14. Scrive in solution_text le soluzioni, nella variabile name, della
 * condizione periodica f ristretta da finestre, e riempie trig_arc[] con i
 * loro intervalli, questa volta non ridotti a un periodo. La tabella si
 * legge un giro alla volta, dal giro window_first al giro window_last;
 * pi_truth[j][0] dice se la condizione vale nel punto u = pi del giro
 * window_first + j, che è dove quel giro finisce e il successivo comincia:
 * se vale, unisce l'ultimo intervallo di un giro al primo del successivo.
 * Ritorna 0, dopo aver annotato un errore, se le soluzioni non stanno in un
 * intervallo limitato o se gli intervalli sono troppi. */
static int window_solution(const Formula *f, int name, int pi_truth[][3]) {
    static const char unbounded[] = "le soluzioni di una condizione periodica ristretta dalla variabile non stanno in un intervallo limitato: non le so scrivere";
    Piece piece;
    int carry = -1;  /* l'intervallo che arriva alla fine del giro precedente, punto compreso */
    trig_arcs = 0;
    solution_text[0] = solution_note[0] = '\0';
    for (window_turn = window_first; window_turn <= window_last && !failure; window_turn++) {
        Frac shift = frac_int(2 * window_turn);
        Angle start = {0, frac_int(2 * window_turn - 1), frac_int(0), 0, (double)(2 * window_turn - 1)};
        Angle end = {0, frac_int(2 * window_turn + 1), frac_int(0), 0, (double)(2 * window_turn + 1)};
        int reaches = -1, at_end = pi_truth[window_turn - window_first][0], outer = window_turn == window_first || window_turn == window_last;

        /* Gli intervalli di questo giro. Il primo può continuare quello che
         * il giro precedente ha lasciato aperto. */
        for (int from = 0; !failure && sign_piece(f, from, &piece); from = piece.last + 1) {
            Arc *arc = piece.low < 0 && carry >= 0 ? &trig_arc[carry] : NULL;
            if (outer) { fail(unbounded); break; }
            if (!arc && trig_arcs == MAX_ARCS) { fail("troppi archi nelle soluzioni di una condizione periodica"); break; }
            if (!arc) {
                arc = &trig_arc[trig_arcs++];
                arc->from = piece.low < 0 ? start : angle_turn(angle_of_point(piece.low), shift);
                arc->from_closed = piece.low >= 0 && piece.low_closed;
            }
            arc->single = arc->from_closed && piece.first == piece.last && piece.first % 2 && piece.low >= 0;
            arc->to = piece.high < 0 ? end : angle_turn(angle_of_point(piece.high), shift);
            arc->to_closed = piece.high >= 0 && piece.high_closed;
            carry = -1;
            reaches = piece.high < 0 ? (int)(arc - trig_arc) : -1;
        }
        if (failure) break;

        /* Il punto in cui il giro finisce. */
        if (!at_end) { carry = -1; continue; }
        if (outer) { fail(unbounded); break; }
        if (reaches < 0 && trig_arcs == MAX_ARCS) { fail("troppi archi nelle soluzioni di una condizione periodica"); break; }
        if (reaches < 0) trig_arc[trig_arcs] = (Arc){end, end, 1, 1, 1, frac_int(0)};
        carry = reaches >= 0 ? reaches : trig_arcs++;
        trig_arc[carry].to_closed = 1;
    }
    window_turn = 0;
    if (failure) return 0;

    /* Il testo: gli intervalli sono già in ordine. */
    if (trig_arcs == 0) text_add(solution_text, sizeof solution_text, "\\nexists %c \\in \\mathbb{R}", name);
    for (int a = 0; a < trig_arcs && !failure; a++) {
        const Arc *arc = &trig_arc[a];
        if (a) text_add(solution_text, sizeof solution_text, " \\lor ");
        if (arc->single) {
            text_add(solution_text, sizeof solution_text, "%c = ", name);
            angle_latex(arc->from, frac_int(0), 0, solution_text, sizeof solution_text);
            continue;
        }
        angle_latex(arc->from, frac_int(0), 0, solution_text, sizeof solution_text);
        text_add(solution_text, sizeof solution_text, " %s %c %s ", arc->from_closed ? "\\le" : "<", name, arc->to_closed ? "\\le" : "<");
        angle_latex(arc->to, frac_int(0), 0, solution_text, sizeof solution_text);
    }
    return !failure;
}

/* Ritorna un intervallo che contiene il valore della variabile nell'angolo
 * a, cioè l'angolo diviso per g = trig_scale. */
static Range angle_range(Angle a) {
    Range value = range_mul(range_ratio(a.turns.num, a.turns.den), range_pi());
    if (a.kind == 1) value = range_add(value, range_atan(range_ratio(a.slope.num, a.slope.den)));
    if (a.kind == 2) {
        const Critical *point = &sign_point[a.point];
        Range t = point->exact ? range_ratio(point->low.num, point->low.den) : root_range(&sign_base[point->element], point->low, point->high);
        value = range_add(value, range_mul(range_ratio(2, 1), range_atan(t)));
    }
    return range_div(value, range_ratio(trig_scale.num, trig_scale.den));
}

/* =============================================================================
 * 18.15 IL GRAFICO DELLA TABELLA DEI SEGNI (18q)
 * ============================================================================
 *
 * Di un enunciato deciso con la tabella dei segni si può fare il disegno: è
 * la figura che sui libri accompagna la soluzione di una disequazione. Qui
 * si decide che cosa disegnare; a disegnare e a scrivere il PDF pensa
 * plot.c, che non sa nulla di enunciati.
 *
 *   - Un pannello per ogni confronto della condizione, con le curve dei due
 *     membri (una sola, e l'asse, se l'altro membro è 0).
 *   - In ogni pannello, le fasce verdi dove quel confronto è verificato; e
 *     il campo di esistenza: una fascia grigia dove un membro non ha un
 *     valore, una retta tratteggiata sul suo bordo o su un punto isolato in
 *     cui non lo ha.
 *   - In fondo la retta dei numeri con le soluzioni di tutta la condizione:
 *     un tratto spesso per ogni intervallo, un punto pieno per un estremo
 *     che è una soluzione e uno vuoto per uno che non lo è.
 *
 * Fasce, rette ed estremi vengono dalle righe di sign_row[], cioè dai conti
 * esatti della tabella. I numeri in virgola mobile servono solo a tracciare
 * le curve e a mettere i punti sull'asse: un errore di arrotondamento sposta
 * una linea di un capello, non cambia che cosa è vero. Per questo qui, e
 * solo qui, il motore usa i double.
 */

/* Il grafico dell'ultimo enunciato deciso con la tabella dei segni, o NULL
 * se non ne ha uno. Appartiene al motore, che lo libera quando comincia
 * l'enunciato successivo (prove()); chi scrive il documento lo legge prima.
 * figures_wanted dice se i grafici servono: finché nessuno li mette in un
 * documento non vengono costruiti. */
PlFigure *figure;
int figures_wanted;

/* Ritorna il valore, in virgola mobile, dell'espressione node quando la
 * variabile name vale x: il punto medio dell'intervallo che lo contiene
 * (capitolo 24). Mette 0 in *ok, che chi chiama ha messo a 1, se lì non ha
 * un valore o non lo si sa calcolare. */
static double node_value(const Node *node, int name, double x, int *ok) {
    int undefined = 0;
    Range value = node_range(node, name, (Range){x, x}, &undefined);
    if (undefined || !range_known(value)) { *ok = 0; return 0; }
    return (value.low + value.high) / 2;
}

/* Ritorna il valore della variabile, in virgola mobile, là dove la lettera
 * della tabella vale t: t stesso, oppure, in un enunciato periodico,
 * (2 arctan t) / g, il punto del giro che va da -pi / g a pi / g. */
static double figure_place(double t) {
    if (!trig_on) return t;
    Range angle = range_atan((Range){t, t});
    return (angle.low + angle.high) * (double)trig_scale.den / (double)trig_scale.num;
}

/* Ritorna il valore approssimato della variabile nel punto numero k della
 * tabella, per metterlo su un asse. Una radice irrazionale si avvicina per
 * bisezione sull'elemento della base che la annulla: agli estremi
 * dell'intervallo che la isola il polinomio ha segni opposti, perché la
 * radice è semplice. */
static double point_approx(int k) {
    const Critical *point = &sign_point[k];
    double low = (double)point->low.num / (double)point->low.den, high = (double)point->high.num / (double)point->high.den;
    if (point->exact) return figure_place(low);
    if (point->kappa >= 0) return (low + high) / 2;
    const Uni *q = &sign_base[point->element];
    int negative = 0;
    for (int step = 0; step <= 60; step++) {
        /* Il valore del polinomio nel punto da provare, con la regola di
         * Horner; al passo 0 il punto è l'estremo inferiore. */
        double x = step ? (low + high) / 2 : low, value = 0;
        for (int i = q->degree; i >= 0; i--) value = value * x + (double)q->c[i];
        if (!step) negative = value < 0;
        else if ((value < 0) == negative) low = x;
        else high = x;
    }
    return figure_place((low + high) / 2);
}

/* Mette in list[], che ha MAX_PANELS + 1 posti, i confronti della
 * condizione f nell'ordine in cui sono scritti, e ne aggiorna il numero
 * *count; oltre MAX_PANELS + 1 smette di contare. */
void comparisons_collect(const Formula *f, const Formula **list, int *count) {
    if (!f || *count > MAX_PANELS) return;
    if (f->kind == F_EQUAL || f->kind == F_DISTINCT || f->kind == F_LESS || f->kind == F_LESS_EQ) { list[(*count)++] = f; return; }
    comparisons_collect(f->a, list, count);
    comparisons_collect(f->b, list, count);
}

/* Confronto tra double per qsort. */
static int double_order(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}

/* Ritorna 1 se nella riga row della tabella il confronto f ha un valore. */
static int row_defined(const Formula *f, int row) {
    int defined = 1;
    sign_compare(f, sign_row[row].sign, &defined);
    return defined;
}

/* Ritorna 1 se il punto numero k della tabella è un bordo del campo di
 * esistenza del confronto f: da una parte il confronto ha un valore e
 * dall'altra no, oppure non lo ha solo nel punto. */
static int point_edge(const Formula *f, int k) {
    int before = row_defined(f, 2 * k), here = row_defined(f, 2 * k + 1), after = row_defined(f, 2 * k + 2);
    return before != after || (!here && before);
}

/* Disegna in axes, tra low e high, il pannello del confronto f nella
 * variabile name: le due curve, le fasce verdi dove vale, quelle grigie e
 * le rette tratteggiate dove non ha un valore. title è il titolo del
 * pannello. */
static void figure_panel(PlAxes *axes, const Formula *f, int name, double low, double high, const char *title) {
    static double xs[FIGURE_SAMPLES + MAX_POINTS], left[FIGURE_SAMPLES + MAX_POINTS], right[FIGURE_SAMPLES + MAX_POINTS], seen[2 * FIGURE_SAMPLES];
    volatile double zero = 0;
    double hole = zero / zero;  /* "non un numero": dove plot.c spezza una linea */

    /* I due membri come sono scritti: il lettore scambia quelli di > e \ge. */
    const Node *first = f->swapped ? f->right : f->left, *second = f->swapped ? f->left : f->right;
    int count = 0, values = 0, next = 0, flat = second->kind == N_NUM && second->value == 0;

    /* I campioni, da sinistra. Passando su un punto in cui il confronto non
     * è definito si mette un buco e una retta tratteggiata: senza il buco la
     * linea unirebbe i due rami di un asintoto. */
    for (int i = 0; i < FIGURE_SAMPLES; i++) {
        double x = low + (high - low) * i / (FIGURE_SAMPLES - 1);
        for (; next < sign_points_count && point_approx(next) <= x; next++) {
            if (point_edge(f, next)) pl_axvline(axes, point_approx(next), PL_GRAY, 0.8, 1);
            if (row_defined(f, 2 * next + 1)) continue;
            xs[count] = point_approx(next);
            left[count] = right[count] = hole;
            count++;
        }
        int ok = 1;
        double l = node_value(first, name, x, &ok), r = node_value(second, name, x, &ok);

        /* Un valore fuori dai double (infinito, o "non un numero") vale come
         * un buco: sottratto a se stesso non dà zero. */
        if (l - l != 0 || r - r != 0) ok = 0;
        xs[count] = x;
        left[count] = ok ? l : hole;
        right[count] = ok ? r : hole;
        count++;
        /* Per l'asse y contano i campioni della parte centrale: ai lati
         * c'è solo il margine, dove un polinomio è già cresciuto molto. */
        if (!ok || 8 * i < FIGURE_SAMPLES || 8 * i > 7 * FIGURE_SAMPLES) continue;
        seen[values++] = l;
        if (!flat) seen[values++] = r;
    }

    /* L'asse y: i valori centrali delle curve, più un margine. Vicino a un
     * asintoto i valori crescono senza limite, e prendendoli tutti il resto
     * del grafico si schiaccerebbe sull'asse: si tengono quelli tra il primo
     * e l'ultimo decimo, e la cornice taglia il resto. */
    double bottom = -1, top = 1;
    if (values > 0) {
        qsort(seen, (size_t)values, sizeof *seen, double_order);
        bottom = seen[values / 10];
        top = seen[values - 1 - values / 10];
        if (flat && bottom > 0) bottom = 0;
        if (flat && top < 0) top = 0;
        double margin = (top - bottom) / 2;
        if (margin < 0.5) margin = 0.5;
        bottom -= margin;
        top += margin;
    }
    pl_set_title(axes, title);
    pl_set_xlim(axes, low, high);
    pl_set_ylim(axes, bottom, top);

    /* Dove il confronto non ha valore: una fascia grigia per ogni tratto di
     * righe consecutive in cui non è definito. Un punto solo, come uno zero
     * del denominatore, ha già la sua retta tratteggiata. */
    for (int row = 0; row < sign_rows; row++) {
        int last = row;
        if (row_defined(f, row)) continue;
        while (last + 1 < sign_rows && !row_defined(f, last + 1)) last++;
        /* La riga r comincia nel punto (r - 1) / 2 e finisce nel punto
         * r / 2, che per una riga dispari sono lo stesso punto; la prima e
         * l'ultima arrivano ai bordi dell'asse. */
        if (last > row || row % 2 == 0)
            pl_axvspan(axes, row == 0 ? low : point_approx((row - 1) / 2), last == sign_rows - 1 ? high : point_approx(last / 2), PL_GRAY);
        row = last;
    }

    /* Dove il confronto vale: una fascia per ogni intervallo, un punto sulla
     * curva per una soluzione isolata. */
    Piece piece;
    for (int from = 0; sign_piece(f, from, &piece); from = piece.last + 1) {
        double a = piece.low < 0 ? low : point_approx(piece.low), b = piece.high < 0 ? high : point_approx(piece.high);
        int ok = 1;
        if (piece.first == piece.last && piece.first % 2) pl_marker(axes, a, node_value(first, name, a, &ok), PL_GREEN, 1);
        else pl_axvspan(axes, a, b, PL_GREEN);
    }

    /* Le curve: i due membri, o un membro e l'asse se l'altro è 0. */
    if (flat) pl_axhline(axes, 0, PL_BLACK, 0.8, 0);
    pl_plot(axes, xs, left, count, PL_BLUE, 1.5, "left side");
    if (!flat) pl_plot(axes, xs, right, count, PL_ORANGE, 1.5, "right side");
    pl_legend(axes);
}

/* Disegna in axes, tra low e high, la retta dei numeri con le soluzioni
 * della condizione f: un tratto spesso per ogni intervallo, e ai suoi
 * estremi un punto pieno se l'estremo è una soluzione, vuoto se non lo è.
 * Sulle tacche stanno gli estremi: i razionali esatti, gli altri con tre
 * decimali. */
static void figure_solutions(PlAxes *axes, const Formula *f, double low, double high) {
    static double at[MAX_POINTS];
    static char text[MAX_POINTS][32];
    static const char *label[MAX_POINTS];
    int ticks = 0, written = -1;  /* written: l'ultima tacca con la scritta */
    Piece piece;
    pl_set_title(axes, "solutions (full dot: included, empty dot: excluded)");
    pl_set_xlim(axes, low, high);
    pl_set_ylim(axes, -1, 1);
    pl_set_yticks(axes, NULL, NULL, 0);
    pl_axhline(axes, 0, PL_GRAY, 0.8, 0);
    for (int from = 0; sign_piece(f, from, &piece); from = piece.last + 1) {
        double ends[2] = {piece.low < 0 ? low : point_approx(piece.low), piece.high < 0 ? high : point_approx(piece.high)}, level[2] = {0, 0};
        int single = piece.first == piece.last && piece.first % 2;
        if (!single) pl_plot(axes, ends, level, 2, PL_GREEN, 4, NULL);

        /* Gli estremi: i punti, con la loro tacca. Un punto solo è l'estremo
         * di se stesso, e si disegna una volta. */
        for (int side = 0; side < (single ? 1 : 2); side++) {
            int k = side ? piece.high : piece.low;
            if (k < 0) continue;
            pl_marker(axes, ends[side], 0, PL_GREEN, side ? piece.high_closed : piece.low_closed);
            if (ticks > 0 && at[ticks - 1] == ends[side]) continue;
            /* In un enunciato periodico il punto esatto è il valore di t,
             * non quello della variabile: lì la scritta è sempre il
             * decimale. */
            if (sign_point[k].exact && !trig_on) wide_text(sign_point[k].low, text[ticks], sizeof text[ticks]);
            else snprintf(text[ticks], sizeof text[ticks], "%.3f", ends[side]);

            /* Due estremi vicini avrebbero le scritte una sull'altra: il
             * secondo resta con la sola tacca, e il suo valore si legge
             * nelle soluzioni scritte. È una stima: un carattere è largo
             * circa 0,08 pollici e l'asse circa 5, la misura vera la conosce
             * solo plot.c. */
            if (written >= 0 && (ends[side] - at[written]) / (high - low) * 5 < 0.04 * (double)(strlen(text[written]) + strlen(text[ticks])) + 0.1) text[ticks][0] = '\0';
            else written = ticks;
            at[ticks] = ends[side];
            label[ticks] = text[ticks];
            ticks++;
        }
    }
    pl_set_xticks(axes, at, label, ticks);
}

/* Ritorna 1 se nel punto numero k della tabella la condizione f cambia: se
 * lì vale e subito prima o subito dopo no, o il contrario. */
static int point_matters(const Formula *f, int k) {
    int truth[3];
    for (int i = 0; i < 3; i++) truth[i] = sign_row[2 * k + i].inside && sign_truth(f, sign_row[2 * k + i].sign);
    return truth[0] != truth[1] || truth[1] != truth[2];
}

/* 18q. Costruisce in `figure` il grafico della condizione f nella variabile
 * name, dalla tabella dei segni appena riempita. Se la condizione ha più di
 * MAX_PANELS confronti, o manca la memoria, non lo costruisce. */
static void sign_figure(const Formula *f, int name) {
    const Formula *panel[MAX_PANELS + 1];
    int panels = 0;
    comparisons_collect(f, panel, &panels);
    if (panels == 0 || panels > MAX_PANELS) return;

    /* L'asse x: dal primo all'ultimo punto in cui cambia qualcosa, con un
     * margine; se non ce ne sono, un intervallo attorno allo zero. Non tutti
     * i punti della tabella contano: con i valori assoluti ci sono anche le
     * radici delle scelte di segno che in quel punto non valgono, e
     * comprenderle allargherebbe l'asse fino a schiacciare ciò che si vuole
     * vedere. */
    double low = -5, high = 5;
    int seen = 0;
    for (int k = 0; k < sign_points_count && !trig_on; k++) {
        int matters = point_matters(f, k);
        for (int i = 0; i < panels && !matters; i++) matters = point_edge(panel[i], k) || point_matters(panel[i], k);
        if (!matters) continue;
        if (!seen++) low = point_approx(k);
        high = point_approx(k);
    }
    if (seen) {
        double margin = (high - low) / 2;
        if (margin < 2) margin = 2;
        low -= margin;
        high += margin;
    }

    /* Di un enunciato periodico si disegna un periodo: il giro della
     * tabella, da -pi / g a pi / g, dove t percorre tutta la retta. */
    if (trig_on) {
        Range pi = range_pi();
        high = (pi.low + pi.high) / 2 * (double)trig_scale.den / (double)trig_scale.num;
        low = -high;
    }

    /* I pannelli dei confronti, poi la retta delle soluzioni. */
    figure = pl_figure(6.4, 1.2 + 1.9 * panels);
    if (!figure) return;
    for (int k = 0; k <= panels; k++) {
        char title[64];
        PlAxes *axes = pl_add_axes(figure, k < panels ? 1 : 0.3);
        if (!axes) { pl_close(figure); figure = NULL; return; }
        if (k == panels) { figure_solutions(axes, f, low, high); break; }
        snprintf(title, sizeof title, panels > 1 ? "comparison %d (green: where it holds)" : "green: where the comparison holds", k + 1);
        figure_panel(axes, panel[k], name, low, high, title);
    }
}

/* =============================================================================
 * 18.16 IL VERDETTO DELLA TABELLA E IL SUO CERTIFICATO (18p, 18p-15)
 * ============================================================================
 *
 * Il punto di ingresso della regola 18p. Quali enunciati le spettano
 * (formula_needs_signs(), che usa il capitolo 19 per scegliere la regola) e
 * quali sa trattare; poi decide_by_signs(), che mette in fila i capitoli
 * precedenti: prepara i confronti, trova i punti, riempie e ricontrolla la
 * tabella, scrive la dimostrazione una riga alla volta, e ne trae il
 * verdetto o le soluzioni. Infine la tabella diventa un certificato, che
 * checker.c ricontrolla per conto suo (sign_certify()).
 */

/* Ritorna 1 se nell'enunciato f compare una relazione d'ordine o un
 * quantificatore sui numeri reali, o se f chiede un insieme di soluzioni:
 * ciò che solo la tabella dei segni tratta. */
int formula_needs_signs(const Formula *f) {
    if (!f) return 0;
    if (f->kind == F_LESS || f->kind == F_LESS_EQ || f->kind == F_SOLVE) return 1;
    if ((f->kind == F_FORALL || f->kind == F_EXISTS) && f->numbers.reals) return 1;
    return formula_needs_signs(f->a) || formula_needs_signs(f->b);
}

/* Ritorna 1 se in f compare un quantificatore. */
static int formula_has_quantifier(const Formula *f) {
    if (!f) return 0;
    return f->kind == F_FORALL || f->kind == F_EXISTS || formula_has_quantifier(f->a) || formula_has_quantifier(f->b);
}

/* Ritorna 1 se in f compare un quantificatore che la tabella dei segni non
 * tratta: ogni quantificatore tranne quelli su un intero, senza altri
 * quantificatori dentro, che descrivono famiglie di soluzioni (18p-13). */
static int formula_bad_quantifier(const Formula *f) {
    if (!f) return 0;
    if (family_owner(f)) return formula_has_quantifier(f->a);
    return f->kind == F_FORALL || f->kind == F_EXISTS || formula_bad_quantifier(f->a) || formula_bad_quantifier(f->b);
}

/* Comincia una tabella dei segni nella variabile di nome name: svuota le
 * colonne, i confronti preparati, gli alberi, gli spazi, le famiglie e le
 * finestre della tabella precedente, e spegne le funzioni goniometriche. Chi
 * chiama sceglie poi la lettera della tabella (sign_x) e, per un enunciato
 * periodico, accende trig_on. La usano decide_by_signs() e la regola del
 * parametro (18t), che prepara una tabella nella lettera del parametro: lo
 * stato da cui partono è così lo stesso. */
static void sign_reset(int name) {
    sign_atoms = sign_polys = sign_nodes = sign_needs = kappas = spaces = family_leaves = windows = 0;
    window_first = window_last = window_turn = 0;
    sign_name = name;
    trig_on = 0;
}

/* Ritorna l'enunciato f senza le negazioni che lo precedono, e mette in
 * *negated 1 se erano in numero dispari: allora f afferma il contrario di
 * ciò che resta. */
const Formula *without_negations(const Formula *f, int *negated) {
    *negated = 0;
    while (f->kind == F_NOT) { f = f->a; *negated = !*negated; }
    return f;
}

/* Chiude la dimostrazione di un "per ogni" o di un "esiste" deciso da una
 * tabella dei segni, riga per riga, o dalle celle di un parametro: holds
 * dice se è vero ciò che resta dell'enunciato tolte le negazioni
 * (without_negations()), negated se le negazioni erano dispari. Riempie
 * l'esito di *verdict, con il controesempio where se l'enunciato è falso e
 * una riga, o una cella, lo ha mostrato (altrimenti where è NULL). */
static void claim_verdict(Verdict *verdict, int holds, int negated, const char *where) {
    if (negated) proof_add(" The statement is the negation of this claim.");
    proof_add(holds != negated ? " $\\Box$" : " So the statement is false.");
    verdict->outcome = holds != negated ? PROVED : REFUTED;
    verdict->detail = verdict->outcome == REFUTED ? where : NULL;
    verdict->proof = proof_text;
}

/* Scrive in where, di size byte, il valore della variabile name nella riga
 * row della tabella, quella che ha deciso l'enunciato: è il controesempio, o
 * l'esempio, che il verdetto riporta. shown è la lettera della tabella (t in
 * un enunciato periodico) e turn_text il giro in cui si legge la riga
 * (18p-14), come testo da aggiungere al valore; vuoto per il giro 0. */
static void row_where(int row, int name, int shown, const char *turn_text, char *where, size_t size) {
    const SignRow *r = &sign_row[row];
    if (trig_on) {
        /* Il valore della variabile: (2 / g) arctan t. */
        char value[96] = "", factor[48] = "";
        Frac twice = frac_div(frac_int(2), trig_scale);
        if (twice.den != 1) snprintf(factor, sizeof factor, "\\frac{%lld}{%lld}", twice.num, twice.den);
        else if (twice.num != 1) snprintf(factor, sizeof factor, "%lld", twice.num);
        solution_note[0] = '\0';

        /* Un punto della tabella che è un angolo riconosciuto (18p-12) si
         * scrive come tale: x = \frac{\pi}{3}, non 4\arctan(2 - \sqrt{3}). */
        Angle angle = row % 2 ? angle_of_point(row / 2) : (Angle){2, frac_int(0), frac_int(0), 0, 0};
        if (angle.kind != 2) {
            snprintf(where, size, "%c = ", name);
            angle_latex(angle_turn(angle, frac_int(2 * window_turn)), frac_int(0), 0, where, size);
            return;
        }
        if (row % 2) point_latex(row / 2, shown, value, sizeof value); else wide_latex(r->sample, value, sizeof value);
        if (failure || solution_note[0]) snprintf(where, size, "%c = %s\\arctan t%s, con t una radice irrazionale di un polinomio della tabella", name, factor, turn_text);
        else if (strcmp(value, "0") == 0) snprintf(where, size, "%c = %s", name, turn_text[0] ? turn_text + (window_turn < 0 ? 1 : 3) : "0");
        else snprintf(where, size, "%c = %s\\arctan\\left(%s\\right)%s", name, factor, value, turn_text);
        failure = NULL;
    } else if (!r->rational) {
        /* Una radice irrazionale: con i radicali, se ha una scrittura. */
        char low[48], high[48], value[96] = "";
        wide_text(sign_point[row / 2].low, low, sizeof low);
        wide_text(sign_point[row / 2].high, high, sizeof high);
        solution_note[0] = '\0';
        point_latex(row / 2, name, value, sizeof value);
        if (!failure && !solution_note[0]) snprintf(where, size, "%c = %s", name, value);
        else snprintf(where, size, "%c = il numero irrazionale tra %s e %s che annulla un polinomio dell'enunciato", name, low, high);
        failure = NULL;
    } else {
        char value[48];
        wide_text(r->sample, value, sizeof value);
        snprintf(where, size, "%c = %s", name, value);
    }
}

/* 18p-12. Le soluzioni della condizione periodica body nella variabile name,
 * dalla tabella appena riempita, e il loro controllo; pi_truth[] è la verità
 * della condizione nel punto u = pi di ogni giro letto (vedi
 * window_solution()), opening il punto della dimostrazione da cui comincia
 * la tabella, da cancellare se il controllo non riesce. Riempie *verdict.
 *
 * Ciò che si è scritto lo si rilegge, con il lettore del programma, come
 * "esiste k intero tale che ..."; poi in molti valori della variabile,
 * sparsi su più periodi, il testo riletto e la condizione, calcolati con i
 * numeri, devono dire la stessa cosa. È il controllo di tutto il ritorno da
 * t a x: angoli riconosciuti, periodo, estremi compresi o no, e la
 * scrittura. */
static void periodic_solutions(const Formula *body, int name, int pi_truth[][3], size_t opening, Verdict *verdict) {
    if (!(windows ? window_solution(body, name, pi_truth) : trig_solution(body, name, pi_truth[0][0]))) { verdict->reason = failure; failure = NULL; proof_cut(opening); return; }
    static char wrapped[sizeof solution_text + 64];
    const Formula *written = NULL;
    int checked = 0, family = strstr(solution_text, "k\\pi") != NULL, plain = (family || (windows && trig_arcs > 0)) && !solution_note[0];
    if (plain) {
        snprintf(wrapped, sizeof wrapped, family ? "\\exists k \\in \\mathbb{Z}\\ \\left(%s\\right)" : "%s", solution_text);
        written = condition_reread(wrapped);
    }

    /* I valori di prova, in giri di pi di u: sparsi su quasi quattro
     * periodi, oppure, con le finestre, su tutti i giri letti. Poi gli
     * estremi scritti, dove si vede un < al posto di un \le: lì i due conti
     * possono solo dire "uguale, a quanto si vede", e devono dirlo tutti e
     * due. */
    long long first = 2 * window_first - 1, span = 2 * (window_last - window_first) + 2;
    for (int i = 0; i < 97 + 2 * trig_arcs && plain; i++) {
        Range value;
        int edge = i >= 97;
        if (edge) value = angle_range((i - 97) % 2 ? trig_arc[(i - 97) / 2].to : trig_arc[(i - 97) / 2].from);
        else if (windows) value = range_div(range_mul(range_ratio(first * 97000 + span * (1000 * i + 371), 97000), range_pi()), range_ratio(trig_scale.num, trig_scale.den));
        else value = range_div(range_mul(range_ratio(-3700000 + 82291 * i, 1000000), range_pi()), range_ratio(trig_scale.num, trig_scale.den));
        int member = written ? range_truth(written, name, value, edge) : -1, seen = range_truth(body, name, value, edge);
        if (member < 0 || seen < 0) continue;
        checked += !edge;
        if (member == seen) continue;
        unjustified_steps++;
        proof_cut(opening);
        verdict->outcome = NOT_PROVED;
        verdict->reason = "le soluzioni scritte non coincidono con la condizione, calcolata con i numeri";
        return;
    }
    if (plain && checked < 40) { proof_cut(opening); verdict->reason = "non riesco a ricontrollare con i numeri le soluzioni di una condizione periodica"; return; }
    proof_add("Going back to $%c$, the condition holds exactly for $%s$%s. $\\Box$", name, solution_text, family ? ", with $k$ any integer" : "");
    verdict->outcome = SOLVED;
    verdict->detail = solution_text;
    verdict->note = family ? "k intero" : NULL;
    if (solution_note[0]) {
        static char note[sizeof solution_note + 128];
        snprintf(note, sizeof note, "%sradici senza una scrittura con i radicali: le soluzioni scritte non sono state rilette%s", family ? "k intero; " : "", solution_note);
        verdict->note = note;
    }
    verdict->proof = proof_text;
}

/* Le soluzioni della condizione body, non periodica, nella variabile name,
 * dalla tabella appena riempita: sign_solution() le scrive, e
 * solution_reread() le rilegge e le confronta con la tabella. opening è il
 * punto della dimostrazione da cui comincia la tabella, da cancellare se il
 * controllo non riesce. Riempie *verdict. */
static void table_solutions(const Formula *body, int name, size_t opening, Verdict *verdict) {
    int plain = sign_solution(body, name);
    if (failure) { verdict->reason = failure; failure = NULL; proof_cut(opening); return; }
    if (plain && !solution_reread(body, name)) {
        unjustified_steps++;
        proof_cut(opening);
        verdict->outcome = NOT_PROVED;
        verdict->reason = "le soluzioni scritte, rilette, non coincidono con la tabella dei segni";
        return;
    }
    proof_add("Hence the condition holds exactly for $%s$. $\\Box$", solution_text);
    verdict->outcome = SOLVED;
    verdict->detail = solution_text;
    if (solution_note[0]) {
        static char note[sizeof solution_note + 96];
        snprintf(note, sizeof note, "radici senza una scrittura con i radicali: le soluzioni scritte non sono state rilette%s", solution_note);
        verdict->note = note;
    }
    verdict->proof = proof_text;
}

/* 18p. Decide con la tabella dei segni l'enunciato thesis, che deve avere la
 * forma: eventuali negazioni, un quantificatore su una variabile che varia
 * nei reali o nei razionali, una condizione senza altri quantificatori;
 * oppure essere l'insieme delle soluzioni di una condizione così, nei reali.
 * Riempie *verdict, con la dimostrazione scritta e il controesempio o le
 * soluzioni. */
void decide_by_signs(const Formula *thesis, Verdict *verdict) {
    static char where[160];
    int negated;
    const Formula *q = without_negations(thesis, &negated);
    if ((q->kind != F_FORALL && q->kind != F_EXISTS && q->kind != F_SOLVE) || formula_bad_quantifier(q->a) || q->numbers.integers) {
        verdict->reason = "le relazioni d'ordine e i numeri reali sono trattati solo con una variabile, sui reali o sui razionali";
        return;
    }
    if (q->kind == F_SOLVE && !q->numbers.reals) { verdict->reason = "un insieme di soluzioni si cerca solo nei numeri reali"; return; }
    const Formula *body = q->a;
    const NumberSet *set = &q->numbers;
    int every = q->kind == F_FORALL, solving = q->kind == F_SOLVE, name = q->variable, x = atom_var(name), shown = name;
    static int pi_truth[MAX_TURNS][3];
    char pi_text[64] = "";

    /* 18p-11. Un enunciato con funzioni goniometriche della variabile è
     * periodico: la tabella si fa nella lettera t = tan(g x / 2), che da qui
     * in poi prende il posto della variabile, e il punto g x = pi, dove t
     * non ha un valore, si calcola subito, a parte: lì ogni funzione è un
     * numero, e l'enunciato è vero o falso senza tabella. */
    sign_reset(name);
    trig_bad = 0;
    trig_scale = frac_int(0);
    trig_x = x;
    formula_trig(body);
    failure = NULL;
    if (trig_scale.num != 0) {
        if (trig_bad || !set->reals || set->bounded || set->holes) {
            verdict->reason = "le funzioni goniometriche sono trattate su tutti i numeri reali, con argomenti a x + b \\pi";
            return;
        }
        int constant[MAX_CRITICAL];
        trig_on = 1;
        trig_letter = atom_var(SURD_NAMES + MAX_SURDS + MAX_SPACES);
        trig_root[0] = node_call(FN_ROOT, node_num(2), node_num(2));
        trig_root[1] = node_call(FN_ROOT, node_num(3), node_num(2));
        x = sign_x = trig_letter;
        shown = 't';
        trig_at_pi = 1;
        sign_prepare(body, x);
        trig_at_pi = 0;
        for (int i = 0; i < sign_polys && !failure; i++) {
            if (sign_poly[i].degree > 0) fail(SIGN_SHAPE);
            constant[i] = uni_sign_at(&sign_poly[i], (Wide){0, 1});
        }
        /* 18p-14. Con le finestre i giri da leggere sono più d'uno, e il
         * punto u = pi va calcolato in ognuno. */
        if (windows) { window_first = window_low - 1; window_last = window_high + 1; }
        if (!failure && window_last - window_first >= MAX_TURNS) fail("una condizione periodica ristretta a un intervallo che copre troppi periodi");
        if (failure) { verdict->reason = failure; failure = NULL; trig_on = 0; return; }
        for (window_turn = window_first; window_turn <= window_last; window_turn++) {
            int *at_pi = pi_truth[window_turn - window_first];
            at_pi[0] = sign_truth(body, constant);
            at_pi[1] = body->kind == F_IFF && sign_truth(body->a, constant);
            at_pi[2] = body->kind == F_IFF && sign_truth(body->b, constant);

            /* Il controllo con i numeri, nel punto x = (2j + 1) pi / g. */
            Range pi_point = range_div(range_mul(range_ratio(2 * window_turn + 1, 1), range_pi()), range_ratio(trig_scale.num, trig_scale.den));
            int seen = range_truth(body, name, pi_point, 1);
            if (seen < 0 || seen == at_pi[0]) continue;
            unjustified_steps++;
            trig_on = 0;
            window_turn = 0;
            verdict->outcome = NOT_PROVED;
            verdict->reason = "la verifica indipendente, con i numeri, non conferma il conto nel punto in cui la tangente non è definita";
            return;
        }
        window_turn = 0;
        sign_atoms = sign_polys = sign_nodes = sign_needs = family_leaves = windows = 0;
    } else if (formula_has_quantifier(body)) {
        verdict->reason = "un intero k dentro l'enunciato è trattato solo per scrivere le soluzioni di una condizione periodica, come x = a + k T";
        return;
    }

    /* 18p-1. I confronti; poi i punti che delimitano l'insieme: il suo
     * estremo inferiore e i punti tolti. */
    sign_x = x;

    /* 18p-8. Gli spazi: prima si registrano, guardando tutti i confronti;
     * un errore in questa lettura non conta, lo ridirà il conto vero. In un
     * enunciato periodico non se ne registrano: esponenziali e logaritmi
     * della variabile lì non sono trattati. */
    space_live = !trig_on;
    if (!trig_on) formula_spaces(body);
    space_live = 0;
    failure = NULL;
    sign_prepare(body, x);

    /* I gradini degli spazi, dall'ultimo al primo: i confronti che ne
     * nascono possono contenere solo le lettere degli spazi precedenti, più
     * interni, che così vengono dopo e li trovano già tra le colonne. */
    for (int s = spaces - 1; s >= 0 && !failure; s--) space_process(s, name, x);
    int hole_column[MAX_HOLES], floor_column = failure ? -1 : set_columns(set, hole_column);

    /* 18p-2, 18p-3, 18p-4. I punti, poi la tabella. */
    if (!failure) sign_points(-1);
    int sound = failure ? 1 : sign_table(body, name, set, floor_column, hole_column);
    if (failure) { verdict->reason = failure; failure = NULL; return; }
    if (!sound) {
        unjustified_steps++;
        verdict->outcome = NOT_PROVED;
        verdict->reason = "la verifica indipendente, con i numeri, non conferma la tabella dei segni";
        return;
    }

    /* La dimostrazione scritta: una riga alla volta, da sinistra, finché una
     * decide. Una riga decide quando smentisce un "per ogni" o conferma un
     * "esiste"; per un insieme di soluzioni servono tutte. */
    size_t opening = proof_length;
    int decided = -1, rechecked = 1;
    if (trig_on) {
        /* La sostituzione, detta al lettore: da qui la tabella è in t. */
        char angle[48] = "x";
        if (trig_scale.den != 1) snprintf(angle, sizeof angle, "\\frac{%lld}{%lld} %c", trig_scale.num, trig_scale.den, name);
        else if (trig_scale.num != 1) snprintf(angle, sizeof angle, "%lld %c", trig_scale.num, name);
        else snprintf(angle, sizeof angle, "%c", name);
        proof_add("\\textbf{Substitution.} Put $u = %s$ and $t = \\tan\\frac{u}{2}$: then $\\sin u = \\frac{2t}{1 + t^{2}}$ and "
                  "$\\cos u = \\frac{1 - t^{2}}{1 + t^{2}}$, and every comparison becomes one between expressions in $t$. As $u$ runs "
                  "over one turn, from $-\\pi$ to $\\pi$, $t$ runs once over the whole real line; the point $u = \\pi$, where $t$ has no "
                  "value, is checked apart. The statement has period $2\\pi$ in $u$.\n\n", angle);
    }
    proof_add("\\textbf{Sign table.} Each comparison counts as false where one of its sides has no value. "
              "Its truth can change only where one of these expressions in $%c$ is zero: ", shown);
    for (int i = 0, written = 0; i < sign_polys; i++) {
        /* Solo le colonne di questa tabella: i polinomi nella variabile, e
         * le differenze x - k. */
        if (sign_space[i] >= 0 || (sign_kappa[i] < 0 && sign_poly[i].degree <= 0)) continue;
        proof_add("%s$", written++ ? ", " : "");
        if (sign_kappa[i] >= 0) proof_add("%c - %s", shown, kappa[sign_kappa[i]].text); else put_uni(&sign_poly[i], shown);
        proof_add("$");
    }
    proof_add(". At each of these points and on every interval between two consecutive ones the signs are constant, so one value of $%c$ decides each.\n\\begin{itemize}\n", shown);
    /* Un giro alla volta (18p-14): senza finestre il giro è uno solo. */
    for (window_turn = window_first; window_turn <= window_last && decided < 0; window_turn++) {
        const int *at_pi = pi_truth[window_turn - window_first];
        char turn_text[64] = "";
        if (window_turn) {
            /* Il giro, come multiplo di pi da aggiungere al valore di x. */
            snprintf(turn_text, sizeof turn_text, window_turn < 0 ? " - " : " + ");
            angle_latex((Angle){0, frac_int(window_turn < 0 ? -2 * window_turn : 2 * window_turn), frac_int(0), 0, 0}, frac_int(0), 0, turn_text, sizeof turn_text);
        }
        if (windows)
            proof_add("\\item[] With $u$ from $%lld\\pi$ to $%lld\\pi$%s:\n", 2 * window_turn - 1, 2 * window_turn + 1,
                      window_turn == window_first ? ", and in the same way on every turn before" : window_turn == window_last ? ", and in the same way on every turn after" : "");
        for (int row = 0; row < sign_rows && decided < 0; row++) {
            const SignRow *r = &sign_row[row];
            if (!r->inside) continue;
            int truth = sign_truth(body, r->sign);
            proof_add("\\item ");
            put_row(row, shown);
            if (body->kind == F_IFF)
                proof_add(": the left side is %s, the right side is %s.\n", sign_truth(body->a, r->sign) ? "true" : "false", sign_truth(body->b, r->sign) ? "true" : "false");
            else
                proof_add(": the condition %s.\n", truth ? "holds" : "fails");

            /* Una riga razionale che il conto con i numeri non ha potuto
             * confermare lascia l'enunciato non deciso: un risultato non
             * verificato non è un risultato. */
            if (r->must && !r->confirmed) rechecked = 0;
            if (solving || truth == every) continue;
            decided = row;
            row_where(row, name, shown, turn_text, where, sizeof where);
        }

        /* In un enunciato periodico, il punto lasciato fuori dalla tabella. */
        if (trig_on && decided < 0) {
            pi_text[0] = '\0';
            angle_latex((Angle){0, frac_int(2 * window_turn + 1), frac_int(0), 0, 0}, frac_int(0), 0, pi_text, sizeof pi_text);
            proof_add("\\item $%c = %s$, where $t$ has no value", name, pi_text);
            if (body->kind == F_IFF) proof_add(": the left side is %s, the right side is %s.\n", at_pi[1] ? "true" : "false", at_pi[2] ? "true" : "false");
            else proof_add(": the condition %s.\n", at_pi[0] ? "holds" : "fails");
            if (!solving && at_pi[0] != every) {
                decided = sign_rows;
                snprintf(where, sizeof where, "%c = %s", name, pi_text);
            }
        }
    }
    window_turn = 0;
    proof_add("\\end{itemize}\n");
    if (!rechecked) {
        proof_cut(opening);
        verdict->reason = "non riesco a ricontrollare con i numeri una riga della tabella dei segni: numeri troppo grandi, o una radice dentro un'altra";
        return;
    }
    verdict->method = "con la tabella dei segni";

    /* Il grafico, se serve: della condizione, o del primo membro quando
     * l'enunciato la confronta con il suo risultato. Si fa solo se il conto
     * con i numeri ha confermato ogni riga che deve confermare (must), anche
     * quelle dopo la riga che ha deciso. Di una condizione periodica si
     * disegna un periodo; di una ristretta a un intervallo (18p-14), che si
     * legge un giro alla volta, il grafico non c'è ancora. */
    int drawable = figures_wanted && !windows;
    for (int row = 0; row < sign_rows; row++)
        if (sign_row[row].inside && sign_row[row].must && !sign_row[row].confirmed) drawable = 0;
    if (drawable) sign_figure(body->kind == F_IFF && !solving ? body->a : body, name);

    /* Un insieme di soluzioni: lo si legge dalla tabella, e ciò che si è
     * scritto lo si rilegge. Se una radice non ha una scrittura con i
     * radicali la rilettura non si può fare, e il verdetto lo dice. */
    if (solving && trig_on) { periodic_solutions(body, name, pi_truth, opening, verdict); return; }
    if (solving) { table_solutions(body, name, opening, verdict); return; }

    /* Il verdetto. "Per ogni" è vero se nessuna riga lo smentisce, "esiste"
     * se una lo conferma; una negazione davanti li rovescia. */
    int holds = every ? decided < 0 : decided >= 0;
    if (decided >= 0) proof_add("At this value the condition %s.", every ? "fails" : "holds");
    else proof_add("The condition %s on every row, hence for every value of $%c$ in the set.", every ? "holds" : "fails", shown);
    claim_verdict(verdict, holds, negated, decided >= 0 ? where : NULL);
}

/* 18p-15. IL CERTIFICATO DELLA TABELLA
 *
 * La tabella appena usata da decide_by_signs() diventa un certificato per
 * checker.c (capitolo 12 di checker.c): la condizione, ciò che si afferma, i
 * polinomi che fanno da fattori, e le righe con la verità che la tabella vi
 * ha trovato. Il verificatore non si fida di nulla di questo: ricava da capo
 * i polinomi della condizione e controlla che siano prodotti dei fattori,
 * riconta con Sturm le radici di ogni fattore, ricalcola la verità di ogni
 * riga e ne trae il verdetto.
 *
 * Che cosa si scrive.
 *
 *   - La condizione, con dentro l'insieme su cui varia la variabile quando
 *     non è tutto R o tutto Q: "per ogni x > 0, C" è "per ogni x, x > 0
 *     implica C"; "esiste x > 0 con C" e le soluzioni in R \setminus \{1\}
 *     sono "x > 0 e C", "x \neq 1 e C". Restano due insiemi, reals e
 *     rationals, ed è ciò che il verificatore conosce.
 *   - Ciò che si afferma: per ogni e esiste con la verità dell'enunciato
 *     senza le negazioni davanti, oppure le soluzioni, rilette dal testo
 *     scritto con il lettore del programma: il certificato dice ciò che il
 *     testo dice, non ciò che il motore pensava di scrivere.
 *   - I fattori: x - r per ogni punto razionale, e ogni elemento della base
 *     (18p-4) di grado almeno due, anche senza radici reali. Ogni polinomio
 *     della tabella ne è un prodotto (base_insert()).
 *   - Le righe, con il campione di ogni intervallo, il punto razionale o
 *     l'intervallo che isola una radice, e la verità della condizione.
 *
 * Le risposte. Accettato: il verdetto porta il certificato. Respinto: il
 * motore e il verificatore non sono d'accordo, quindi nel dubbio non è
 * dimostrato, e il passo conta tra quelli che non hanno superato il
 * controllo. Non controllabile, o un enunciato che la notazione non sa dire
 * (radici, esponenziali, logaritmi, funzioni goniometriche, soluzioni con
 * una radice che ha solo un nome): il verdetto resta, e dice perché il
 * certificato manca. */

/* Ritorna 1 se l'espressione node si scrive nella notazione delle tabelle
 * dei segni di checker.c: interi, la variabile name, + - * /, il meno,
 * potenze con un intero scritto all'esponente e valori assoluti. */
int sign_node_plain(const Node *node, int name) {
    switch (node->kind) {
    case N_NUM: return 1;
    case N_VAR: return node->name == name;
    case N_NEG: return sign_node_plain(node->a, name);
    case N_ADD: case N_SUB: case N_MUL: case N_DIV:
        return sign_node_plain(node->a, name) && sign_node_plain(node->b, name);
    case N_POW:
        return (node->b->kind == N_NUM || (node->b->kind == N_NEG && node->b->a->kind == N_NUM)) && sign_node_plain(node->a, name);
    case N_CALL:
        return node->op == FN_ABS && sign_node_plain(node->a, name);
    default:
        return 0;
    }
}

/* Ritorna 1 se la condizione f, senza quantificatori, è fatta di confronti
 * che sign_node_plain() accetta. */
static int sign_formula_plain(const Formula *f, int name) {
    switch (f->kind) {
    case F_EQUAL: case F_DISTINCT: case F_LESS: case F_LESS_EQ:
        return sign_node_plain(f->left, name) && sign_node_plain(f->right, name);
    case F_AND: case F_OR: case F_IMPLIES: case F_IFF:
        return sign_formula_plain(f->a, name) && sign_formula_plain(f->b, name);
    case F_NOT:
        return sign_formula_plain(f->a, name);
    default:
        return 0;
    }
}

/* Scrive la condizione f, senza quantificatori, nella notazione dei
 * certificati. > e \ge sono già < e \le con i membri scambiati.
 *
 * Warning: si appoggia all'ordine di FormulaKind (parser.c): prima i quattro
 * confronti, da F_EQUAL a F_LESS_EQ, poi i connettivi fino a F_NOT. Se
 * cambia, cambia anche qui. */
static void cert_formula(const Formula *f) {
    static const char *const words[] = {[F_EQUAL] = "=", [F_DISTINCT] = "neq", [F_LESS] = "<", [F_LESS_EQ] = "<=",
                                        [F_AND] = "and", [F_OR] = "or", [F_IMPLIES] = "implies", [F_IFF] = "iff", [F_NOT] = "not"};
    if (f->kind > F_NOT) { certificate_broken = 1; return; }
    cert_add("(%s ", words[f->kind]);
    if (f->kind <= F_LESS_EQ) {
        cert_node(f->left);
        cert_add(" ");
        cert_node(f->right);
    } else {
        cert_formula(f->a);
        if (f->b) {
            cert_add(" ");
            cert_formula(f->b);
        }
    }
    cert_add(")");
}

/* Scrive il razionale v; uno che non sta in 64 bit non ha scrittura. */
static void cert_wide(Wide v) {
    if (v.num > LLONG_MAX || v.num < -LLONG_MAX || v.den > LLONG_MAX) certificate_broken = 1;
    else if (v.den == 1) cert_add("%lld", (long long)v.num);
    else cert_add("(/ %lld %lld)", (long long)v.num, (long long)v.den);
}

/* Scrive il polinomio p, che non è nullo, nella lettera name: la somma dei
 * termini dal grado più alto, "(+ primo (+ secondo ...))". */
static void cert_uni(const Uni *p, int name) {
    int terms = 0, written = 0;
    for (int i = 0; i <= p->degree; i++) terms += p->c[i] != 0;
    for (int i = p->degree; i >= 0; i--) {
        __int128 c = p->c[i];
        if (c == 0) continue;
        if (c > LLONG_MAX || c < -LLONG_MAX) certificate_broken = 1;
        if (++written < terms) cert_add("(+ ");
        if (i > 0 && c != 1) cert_add("(* %lld ", (long long)c);
        if (i == 0) cert_add("%lld", (long long)c);
        if (i > 1) cert_add("(^ ");
        if (i > 0) cert_letter(name);
        if (i > 1) cert_add(" %d)", i);
        if (i > 0 && c != 1) cert_add(")");
        if (written < terms) cert_add(" ");
    }
    for (int i = 1; i < terms; i++) cert_add(")");
}

/* Scrive in certificate_text il certificato della tabella con cui
 * decide_by_signs() ha deciso thesis, con il verdetto *verdict; ritorna
 * NULL, oppure il motivo per cui il certificato non c'è. */
static const char *sign_certificate(const Formula *thesis, const Verdict *verdict) {
    int negated;
    const Formula *q = without_negations(thesis, &negated);
    const Formula *body = q->a, *written = NULL;
    const NumberSet *set = &q->numbers;
    int name = q->variable, every = q->kind == F_FORALL, solving = q->kind == F_SOLVE;
    if (!sign_formula_plain(body, name))
        return "la notazione dei certificati della tabella dei segni ha solo frazioni di polinomi e valori assoluti, "
               "non radici, esponenziali, logaritmi o funzioni goniometriche";

    /* Le soluzioni, rilette dal testo; i due testi senza estremi sono le
     * parole all e none. */
    int all = solving && strncmp(solution_text, "\\forall", 7) == 0, none = solving && strncmp(solution_text, "\\nexists", 8) == 0;
    if (solving && solution_note[0]) return "le soluzioni scritte nominano una radice che non ha una scrittura con i radicali";
    if (solving && !all && !none) {
        written = condition_reread(solution_text);
        if (!written) return "le soluzioni scritte non si rileggono";
    }

    /* I posti, in sign_poly[], dei polinomi x - a dell'insieme: già nella
     * tabella, set_columns() li ritrova. */
    int hole_column[MAX_HOLES], floor_column = set_columns(set, hole_column);

    /* La variabile, l'insieme, la condizione con dentro l'insieme. */
    int terms = set->bounded + set->holes;
    certificate_length = 0;
    certificate_broken = 0;
    cert_signs = 1;
    cert_add("certificate signs\nvariable ");
    cert_letter(name);
    cert_add("\ndomain %s\ncondition ", set->reals ? "reals" : "rationals");
    if (terms) cert_add(every ? "(implies " : "(and ");
    for (int i = 0; i < terms; i++) {
        if (i + 1 < terms) cert_add("(and ");
        if (i == 0 && set->bounded) {
            cert_add(set->strict ? "(< %lld " : "(<= %lld ", set->low);
            cert_letter(name);
        } else {
            cert_add("(neq ");
            cert_letter(name);
            cert_add(" ");
            cert_frac(set->hole[i - set->bounded]);
        }
        cert_add(i + 1 < terms ? ") " : ")");
    }
    for (int i = 1; i < terms; i++) cert_add(")");
    if (terms) cert_add(" ");
    cert_formula(body);
    if (terms) cert_add(")");

    /* Ciò che si afferma: la verità dell'enunciato senza le negazioni, o le
     * soluzioni. */
    if (!solving) cert_add("\nclaim %s %s", every ? "forall" : "exists", (verdict->outcome == PROVED) != negated ? "true" : "false");
    else if (written) { cert_add("\nclaim solve\nsolution "); cert_formula(written); }
    else cert_add("\nclaim solve\nsolution %s", all ? "all" : "none");

    /* I fattori: prima x - r per i punti razionali, poi gli elementi della
     * base di grado almeno due; place[k] è il numero dell'elemento k. */
    int place[2 * MAX_CRITICAL], factors = 0;
    for (int k = 0; k < sign_points_count; k++) {
        if (!sign_point[k].exact) continue;
        Uni linear = {1, {-sign_point[k].low.num, sign_point[k].low.den}};
        cert_add("\nfactor ");
        cert_uni(&linear, name);
        factors++;
    }
    for (int k = 0; k < sign_bases; k++) {
        place[k] = 0;
        if (sign_base[k].degree < 2) continue;
        cert_add("\nfactor ");
        cert_uni(&sign_base[k], name);
        place[k] = ++factors;
    }

    /* Le righe, con la verità della condizione: quella del corpo, e
     * l'insieme come è scritto nella condizione. */
    for (int row = 0; row < sign_rows; row++) {
        const SignRow *r = &sign_row[row];
        const Critical *point = &sign_point[row / 2];
        int member = row_in_set(r->sign, set, floor_column, hole_column), truth = sign_truth(body, r->sign);
        if (row % 2 == 0) { cert_add("\ninterval "); cert_wide(r->sample); }
        else if (point->exact) { cert_add("\npoint "); cert_wide(point->low); }
        else {
            /* Una radice irrazionale è di un elemento senza radici
             * razionali, quindi di grado almeno due: ha il suo posto. */
            if (!place[point->element]) certificate_broken = 1;
            cert_add("\nroot %d ", place[point->element]);
            cert_wide(point->low);
            cert_add(" ");
            cert_wide(point->high);
        }
        cert_add(" %s", (every ? !member || truth : member && truth) ? "true" : "false");
    }
    cert_add("\nend\n");
    cert_signs = 0;
    return certificate_broken ? "la tabella ha numeri troppo grandi per la notazione dei certificati, o è troppo lunga" : NULL;
}

/* 18p-15. Fa ricontrollare a checker.c il verdetto *verdict che
 * decide_by_signs() ha dato su thesis, e lo aggiorna con la risposta: vedi
 * "Le risposte" in testa a 18p-15. */
void sign_certify(const Formula *thesis, Verdict *verdict) {
    static char problem[512];
    if (verdict->outcome != PROVED && verdict->outcome != REFUTED && verdict->outcome != SOLVED) return;
    const char *why = sign_certificate(thesis, verdict), *text = certificate_text;
    if (!why) {
        CkAnswer answer = ck_check(&text, &why, checker_steps());
        if (answer == CK_ACCEPTED) { verdict->certificate = certificate_text; return; }

        /* Respinto: nel dubbio non è dimostrato, e il grafico, che illustra
         * la tabella, non si mostra. */
        if (answer == CK_REJECTED) {
            unjustified_steps++;
            snprintf(problem, sizeof problem, "il verificatore indipendente ha respinto il certificato della tabella dei segni: %s", why);
            *verdict = (Verdict){NOT_PROVED, 0, 0, 0, problem, NULL, NULL, NULL, NULL, NULL};
            if (figure) { pl_close(figure); figure = NULL; }
            return;
        }
        snprintf(problem, sizeof problem, "il verificatore non sa controllarlo, %s", why);
        why = problem;
    }

    /* Il motivo si scrive nella riga del verdetto, e per un insieme di
     * soluzioni sta prima del ": " dopo il quale vengono le soluzioni: chi
     * le legge (gli script di tools/fuzz/) le cerca lì. Per questo nel
     * motivo i due punti diventano virgole. */
    if (why != problem) snprintf(problem, sizeof problem, "%s", why);
    for (char *colon = problem; (colon = strchr(colon, ':')) != NULL;) *colon = ',';
    verdict->reason = problem;
}

/* =============================================================================
 * 18.17 UN PARAMETRO (18t): LA PROIEZIONE E LE CELLE
 * ============================================================================
 *
 * Questo capitolo e i due che seguono sono la regola 18t. Qui il metodo e la
 * sua prima metà: i polinomi nelle due lettere, la proiezione (18t-a) e le
 * celle della retta del parametro (18t-b). Il capitolo 18.18 decide ogni
 * cella e ne scrive le soluzioni (18t-c, 18t-d, 18t-e), il 18.19 ricontrolla
 * ciò che si consegna (18t-f, 18t-g, 18t-h) e dà il verdetto.
 *
 * 18t. DUE VARIABILI REALI: UN PARAMETRO
 *
 * A che cosa serve. Sono gli esercizi "con il parametro" dei libri di scuola:
 *
 *     \forall a \in \mathbb{R}\ \{x \in \mathbb{R} \mid x^{2} - 4ax \le 0\}
 *
 * chiede di risolvere la disequazione in x per ogni valore di a, e la
 * risposta è un elenco di casi: per a < 0 le soluzioni sono 4a \le x \le 0,
 * per a = 0 la sola x = 0, per a > 0 sono 0 \le x \le 4a. Le forme trattate
 * sono tre:
 *
 *   - una verifica: un quantificatore sul parametro e, dentro, una
 *     combinazione di confronti nel solo parametro e di enunciati "per ogni
 *     x" o "esiste x"; per esempio \forall a\ \forall x\ (...), oppure
 *     \forall k\ ((\forall x\ (x^{2} - 2kx + 7 > 0)) \iff -\sqrt{7} < k < \sqrt{7});
 *   - i valori del parametro: \{k \in \mathbb{R} \mid \forall x\ (...)\};
 *   - le soluzioni con il parametro, come nell'esempio qui sopra.
 *
 * L'idea. Fissato il parametro a un numero resta un enunciato in una
 * variabile, e quello lo decide la tabella dei segni (18p). I numeri sono
 * infiniti, ma basta provarne pochi: la retta del parametro si divide in
 * "celle", punti e intervalli aperti, e dentro una cella la risposta non
 * cambia. È come guardare una parabola che si sposta al variare di a: finché
 * non cambia verso, e le sue intersezioni con l'asse non nascono, non
 * spariscono e non si scavalcano, la disequazione ha "le stesse" soluzioni,
 * solo spostate. È la scomposizione cilindrica di Collins, con una sola
 * lettera da eliminare.
 *
 *   18t-a. La proiezione: quali valori del parametro separano le celle. Ogni
 *          confronto che contiene x è una frazione di polinomi nelle due
 *          lettere; numeratori, denominatori e divisori si leggono come
 *          polinomi in x i cui coefficienti sono polinomi nel parametro. I
 *          valori critici sono le radici reali di:
 *            a1. il coefficiente direttivo di ognuno;
 *            a2. per ogni f, il primo psc_k(f, f') che non è il polinomio
 *                nullo, con k = 0, 1, ... (f' è la derivata rispetto a x);
 *            a3. per ogni coppia f, g, il primo psc_k(f, g) che non è il
 *                polinomio nullo;
 *            a4. i polinomi dei confronti nel solo parametro, preparati
 *                come per una tabella dei segni nella lettera del parametro
 *                (18p-1, 18p-7).
 *          psc_k è il coefficiente principale del sottorisultante numero k
 *          (subresultant_lead()); psc_0 è il risultante, e psc_0(f, f') è, a
 *          meno del coefficiente direttivo, il discriminante.
 *
 *          Perché bastano. Su un intervallo aperto del parametro in cui
 *          nessuno di quei polinomi si annulla:
 *            - ogni f ha sempre lo stesso grado in x (a1);
 *            - il massimo comun divisore di f e f' ha sempre lo stesso
 *              grado, il primo k con psc_k diverso da zero (a2): quindi f ha
 *              sempre lo stesso numero di radici complesse distinte. Le
 *              radici di un polinomio di grado costante dipendono con
 *              continuità dai coefficienti; se il loro numero non cambia non
 *              possono fondersi né separarsi, e una radice reale non può
 *              diventare complessa, perché prima dovrebbe coincidere con la
 *              sua coniugata. Le radici reali di f sono dunque funzioni
 *              continue del parametro, sempre le stesse e nello stesso
 *              ordine;
 *            - il massimo comun divisore di f e g ha sempre lo stesso grado
 *              (a3): una radice di f e una di g che coincidono in un punto
 *              coincidono in tutto l'intervallo, e due diverse restano
 *              diverse.
 *          Le radici reali di tutti i polinomi sono quindi curve continue
 *          che non si toccano: tagliano la striscia sopra l'intervallo in
 *          fasce, e in ogni fascia e su ogni curva ogni polinomio ha un
 *          segno costante. I segni che x incontra sono gli stessi per ogni
 *          valore del parametro nell'intervallo, e con loro la verità di
 *          "per ogni x" e di "esiste x" (G. E. Collins, Quantifier
 *          elimination for real closed fields by cylindrical algebraic
 *          decomposition, 1975, teoremi 4 e 5). I valori critici non hanno
 *          bisogno di teoria: ognuno è una cella di un punto solo.
 *
 *   18t-b. Le celle: i valori critici in ordine, trovati come i punti di una
 *          tabella dei segni nella lettera del parametro (sign_points()), e
 *          gli intervalli tra due consecutivi, ognuno con un razionale
 *          scelto al suo interno.
 *
 *   18t-c. Una cella, una decisione. Al posto del parametro si scrive il
 *          valore della cella: il razionale scelto, oppure il valore
 *          critico. Uno irrazionale si scrive con la formula risolutiva, se
 *          è radice di un polinomio di secondo grado; altrimenti la regola
 *          rinuncia. Ciò che resta è un enunciato in una variabile, e lo
 *          decide 18p.
 *
 *   18t-d. Il verdetto. "Per ogni a" è vero se lo è in ogni cella, "esiste
 *          a" se lo è in una; i valori del parametro richiesti sono le celle
 *          in cui la condizione vale, scritte come le soluzioni di 18p.
 *
 *   18t-e. Le soluzioni con il parametro. In ogni cella si risolve in x con
 *          il valore della cella. In una cella che è un punto il parametro è
 *          un numero, e gli estremi delle soluzioni anche. In un intervallo
 *          gli estremi vanno scritti in funzione del parametro: sono radici
 *          dei polinomi di 18t-a, e quelle di un polinomio di primo o di
 *          secondo grado in x hanno una formula (i "candidati",
 *          candidates_build()). Ogni estremo trovato con il valore scelto si
 *          riconosce nel solo candidato che lì ha quel valore: il confronto
 *          è esatto, e in un intervallo due candidati diversi non coincidono
 *          mai, per a2 e a3. Le celle vicine con le stesse soluzioni si
 *          scrivono insieme.
 *
 * I controlli indipendenti, oltre a quelli che ogni decisione di 18p porta
 * con sé, sono tre.
 *
 *   18t-f. Ciò che si consegna si rilegge. Il testo delle soluzioni viene
 *          riletto dal lettore del programma come una condizione W. Nel
 *          valore di ogni cella, e in altri due razionali di ogni
 *          intervallo, la tabella dei segni deve dimostrare che la
 *          condizione di partenza e W hanno le stesse soluzioni in x; per i
 *          valori del parametro, W deve valere esattamente nelle celle
 *          trovate. Un estremo riconosciuto male, o un < al posto di un
 *          \le, qui si vedono.
 *
 *   18t-g. La griglia. Le celle poggiano sulla teoria di 18t-a: se alla
 *          proiezione mancasse un valore critico, dentro una cella la verità
 *          potrebbe cambiare senza che il valore scelto lo mostri. Per
 *          questo l'enunciato si guarda anche in valori del parametro presi
 *          senza guardare le celle: tutti i quarti da -PARAM_REACH / 4 a
 *          PARAM_REACH / 4, e i PARAM_GRID razionali più semplici, che vi
 *          aggiungono i terzi. E lo si guarda in due modi. Con la tabella
 *          dei segni, che per quel valore del parametro decide per ogni x:
 *          è lo stesso metodo delle celle, ma in valori che la proiezione
 *          non ha scelto. E con il conto diretto sui numeri
 *          (sign_holds_at()) in PARAM_GRID valori di x, che non usa né la
 *          proiezione né la tabella. Un valore della griglia che smentisce
 *          la cella in cui cade ferma il verdetto. Non è una seconda
 *          dimostrazione, perché la griglia è finita: è un controllo contro
 *          gli errori del programma. Non vede un errore della proiezione che
 *          si mostra solo in un valore del parametro isolato, irrazionale, o
 *          oltre PARAM_REACH / 4: quello lo cerca 18t-h.
 *
 *   18t-h. La proiezione, ricontrollata con un altro conto. È il controllo
 *          su cui poggiano i verdetti che dipendono da tutte le celle (un
 *          "per ogni a" dimostrato, un "esiste a" smentito, ogni RISOLTO):
 *          param_project() registra ogni polinomio che calcola, con la sua
 *          provenienza (ProjectionItem), compresi i psc_k trovati nulli
 *          prima del primo che non lo è, e projection_sound() controlla:
 *            h1. i pezzi: le parti in x di ogni polinomio di param_poly[],
 *                rimoltiplicate per le potenze di x, lo ricompongono; da
 *                loro, e non dall'elenco della proiezione, si ricava quali
 *                polinomi a1, a2 e a3 servono, con il grado in x letto da
 *                capo;
 *            h2. i valori: ogni polinomio che serve si calcola in D + 1
 *                valori razionali del parametro, dove D limita il suo grado,
 *                con un altro algoritmo (il determinante dei numeri, con
 *                l'eliminazione di Bareiss, invece dello sviluppo di Laplace
 *                sui polinomi); il registrato deve esserne un multiplo per
 *                una costante positiva, e un psc_k dichiarato nullo deve
 *                annullarsi in tutti i D + 1. Due polinomi di grado al più D
 *                che coincidono in D + 1 punti sono lo stesso polinomio;
 *            h3. il contenimento: le radici reali distinte di ogni polinomio
 *                che serve, contate con Sturm, sono tante quante i valori
 *                critici che lo annullano, decisi con un conto esatto: tutte
 *                sono quindi valori critici;
 *            h4. le celle: i valori critici sono in ordine e separati; uno
 *                irrazionale è la sola radice del suo polinomio di secondo
 *                grado nel suo intervallo, ed è la radice che il valore della
 *                cella scrive; il razionale di ogni intervallo vi sta dentro.
 *          Con h1-h4 il ragionamento di 18t-a vale per le celle trovate: in
 *          ogni intervallo nessun polinomio della proiezione si annulla, e
 *          il valore scelto decide per tutto l'intervallo. Una discordanza è
 *          un errore del motore: il verdetto non c'è, e unjustified_steps
 *          sale. Un conto che esce dai 128 bit, o un grado oltre
 *          PROJECTION_POINTS - 1, lascia l'enunciato non dimostrato, con il
 *          suo motivo. Che cosa non copre: un polinomio che param_collect()
 *          non ha messo nell'elenco, o che eval() ha calcolato male, perché
 *          h1 parte da param_poly[]; i polinomi a4 dei confronti nel solo
 *          parametro, che prepara sign_prepare() come in una tabella in una
 *          lettera sola; la decisione in ogni cella, che è di 18p con i suoi
 *          controlli; la teoria di 18t-a. E h3 e h4 contano le radici con la
 *          catena di Sturm di 18p-3 (sturm_build()), la stessa che ha
 *          trovato i valori critici: un errore lì sarebbe comune ai due
 *          conti. Ai verdetti che poggiano su una cella sola (un
 *          controesempio, un "esiste a" con il suo valore) non serve, e non
 *          li ferma.
 *
 * Che cosa resta fuori, e il verdetto lo dice: più di due lettere reali una
 * dentro l'altra; insiemi diversi da \mathbb{R}; radici, valori assoluti,
 * logaritmi, potenze e funzioni goniometriche in un confronto che contiene
 * la variabile; gradi in x oltre MAX_PARAM_DEGREE; valori critici
 * irrazionali che non sono radici di un polinomio di secondo grado;
 * soluzioni i cui estremi non sono radici di polinomi di primo o di secondo
 * grado in x. Un enunciato con il parametro non ha grafico: il disegno di
 * 18q è quello di una variabile sola.
 *
 * Il limite su radici e valori assoluti vale anche per una radice o un valore
 * assoluto del solo parametro, quando sta in un confronto con la variabile:
 * la regola scrive soluzioni come 2 - \sqrt{4 - k^{2}} < x, e sa rileggerle
 * un valore del parametro alla volta, ma lo stesso testo dentro un enunciato
 * da verificare non lo tratta. Per trattarlo la proiezione dovrebbe ricevere,
 * di ogni confronto P + Q \sqrt{R} con R nel solo parametro, i polinomi P, Q
 * e P^2 - Q^2 R, come 18p-7 fa in una variabile, e R tra le colonne del
 * parametro; e di un valore assoluto i due polinomi che nascono dai due
 * segni del suo argomento. Andrebbe in param_collect().
 */

/* I limiti di questa regola. Stanno qui, e non nel capitolo 1 con gli altri,
 * perché la regola resti tutta in un blocco.
 *
 * Warning: MAX_MINOR è il doppio di MAX_PARAM_DEGREE, le righe del risultante
 * di due polinomi di quel grado: se alzi il grado alza anche MAX_MINOR, e
 * guarda quanto costa lo sviluppo di minor_determinant(). */
#define MAX_PARAM_POLYS 24   /* polinomi nelle due lettere di un enunciato con il parametro */
#define MAX_PARAM_DEGREE 4   /* il loro grado massimo nella variabile */
#define MAX_MINOR 8          /* righe del determinante più grande: quello di due polinomi di grado 4 */
#define MAX_PARAM_POINTS 48  /* valori critici del parametro */
#define MAX_CANDIDATES 16    /* estremi scritti in funzione del parametro (18t-e) */
#define PARAM_REACH 32       /* la griglia del parametro (18t-g): i quarti da -PARAM_REACH / 4 a PARAM_REACH / 4 */
#define PARAM_GRID 24        /* i razionali più semplici, aggiunti alla griglia del parametro e dati alla variabile nel conto diretto (18t-g) */
#define CELL_TEXT 512        /* lunghezza delle soluzioni di una cella */
#define PARAM_TEXT 4096      /* lunghezza delle soluzioni scritte */
#define PROJECTION_POINTS 64 /* valori del parametro in cui 18t-h calcola un polinomio della proiezione: il suo grado più uno, al più */

/* Quanti polinomi della proiezione si registrano, al più (18t-h): per ogni
 * polinomio il coefficiente direttivo e fino a MAX_PARAM_DEGREE - 1 psc_k con
 * la derivata, per ogni coppia fino a MAX_PARAM_DEGREE psc_k. Sono al più
 * MAX_PARAM_DEGREE per ognuno dei P polinomi e delle P (P - 1) / 2 coppie. */
#define MAX_PROJECTION (MAX_PARAM_DEGREE * MAX_PARAM_POLYS * (MAX_PARAM_POLYS + 1) / 2)

/* I messaggi per ciò che la regola non tratta. */
static const char *const PARAM_FORM =
    "con due lettere reali sono trattati un parametro e una variabile, ognuno su tutto \\mathbb{R}: non tre lettere una dentro l'altra, né altri insiemi";
static const char *const PARAM_SHAPE =
    "con un parametro i confronti che contengono la variabile devono essere tra espressioni razionali nelle due lettere: niente radici, valori assoluti, logaritmi, potenze o funzioni goniometriche";
static const char *const PARAM_DEGREE = "con un parametro i polinomi nella variabile sono trattati fino al quarto grado, e con coefficienti non troppo grandi";
static const char *const PARAM_ROOT = "un valore critico del parametro è un numero irrazionale che non so scrivere con una radice quadrata";
static const char *const PARAM_WRITE = "non so scrivere le soluzioni in funzione del parametro";
static const char *const PARAM_INNER = "la tabella dei segni non decide l'enunciato in un valore del parametro";

/* Ritorna 1 se set è tutto \mathbb{R}, senza estremi né punti tolti. */
static int numbers_all_reals(const NumberSet *set) { return set->reals && !set->bounded && set->holes == 0; }

/* Ritorna il nodo dell'intero v, anche negativo. Il lettore non produce mai
 * un N_NUM negativo, e chi legge gli alberi ci conta: -3 è N_NEG di 3. */
static Node *node_integer(long long v) { return v < 0 ? node_new(N_NEG, node_num(-v), NULL) : node_num(v); }

/* Ritorna il nodo del razionale v. Annota un errore se v non sta nei 64 bit
 * dei numeri di un albero. */
static Node *node_rational(Wide v) {
    if (v.num >= COEF_LIMIT || v.num <= -COEF_LIMIT || v.den >= COEF_LIMIT) { fail(SIGN_LIMIT); return node_num(0); }
    Node *top = node_integer((long long)v.num);
    return v.den == 1 ? top : node_new(N_DIV, top, node_num((long long)v.den));
}

/* 18t-c. Ritorna una copia della condizione f in cui la variabile name è
 * sostituita dall'espressione value, che viene condivisa e non copiata. È
 * formula_substitute() del lettore (capitolo 17) con una lettera sola. name
 * non è legata dentro f: lo garantisce formula_check(), che non ammette due
 * significati per una lettera. */
static Formula *formula_with(const Formula *f, int name, Node *value) {
    const Node *const to[1] = {value};
    return formula_substitute(f, &name, to, 1);
}

/* I polinomi nelle due lettere dell'enunciato in corso (18t-a): numeratori,
 * denominatori e divisori dei confronti che contengono la variabile.
 * param_var[i] è l'atomo della variabile del polinomio i: quella del
 * quantificatore interno in cui sta il suo confronto. param_part[i] sono i
 * suoi coefficienti come polinomio in quella variabile, dal termine noto a
 * quello di grado param_degree[i]; li riempie param_project(). */
static Poly param_poly[MAX_PARAM_POLYS], param_part[MAX_PARAM_POLYS][MAX_PARAM_DEGREE + 1];
static int param_var[MAX_PARAM_POLYS], param_degree[MAX_PARAM_POLYS];
static int param_polys;

/* Aggiunge all'elenco il polinomio p, che viene dal conto di un confronto
 * razionale nel parametro (atomo a) e nella variabile (atomo x). Annota un
 * errore se p contiene altro: un'altra lettera, un esponente non intero, un
 * coefficiente complesso.
 *
 * p può avere esponenti negativi, perché rat_make() porta al numeratore un
 * denominatore di un solo termine: 3/a diventa 3 a^{-1}. Allora lo si
 * moltiplica per la potenza che li toglie, e la lettera che stava a
 * denominatore entra nell'elenco come polinomio a sé: dove si annulla il
 * confronto non ha valore. Un numero non ha radici e non entra; un polinomio
 * già presente, anche a meno di un fattore costante, non si ripete. */
static void param_add(Poly p, int a, int x) {
    const int letter[2] = {a, x};
    long long lowest[2] = {0, 0};
    for (int t = 0; t < p.count; t++) {
        const Term *term = &p.term[t];
        if (term->coef.im.num != 0) { fail(PARAM_SHAPE); return; }
        for (int f = 0; f < term->mono.count; f++) {
            const Factor *factor = &term->mono.factor[f];
            int which = factor->atom == a ? 0 : 1;
            if ((factor->atom != a && factor->atom != x) || factor->exp.den != 1) { fail(PARAM_SHAPE); return; }
            if (factor->exp.num < lowest[which]) lowest[which] = factor->exp.num;
        }
    }
    for (int i = 0; i < 2 && !failure; i++) {
        if (lowest[i] == 0) continue;
        Term power;
        power.coef = num_int(1);
        power.mono = mono_atom(letter[i], frac_int(-lowest[i]));
        p = poly_mul(p, poly_term(power));
        param_add(rat_atom(letter[i]).num, a, x);
    }
    if (failure || poly_is_constant(p)) return;
    for (int i = 0; i < param_polys; i++)
        if (param_var[i] == x && poly_proportional(p, param_poly[i])) return;
    if (param_polys == MAX_PARAM_POLYS) { fail("troppi polinomi diversi in un enunciato con il parametro"); return; }
    param_poly[param_polys] = p;
    param_var[param_polys++] = x;
}

/* 18t-a. Legge i confronti della condizione f, che sta sotto il
 * quantificatore sul parametro di nome a_name. x_name è la lettera del
 * quantificatore interno in cui f si trova, 0 se f sta fuori da tutti.
 *
 * Un confronto senza la variabile va tra quelli della tabella nella lettera
 * del parametro (a4): lo prepara sign_prepare(), con tutto ciò che 18p sa
 * trattare in una lettera sola. Di un confronto con la variabile entrano
 * nell'elenco numeratore, denominatore e divisori della differenza dei due
 * membri. Annota un errore per un quantificatore dentro un altro, per un
 * insieme che non è \mathbb{R}, e per un confronto con la variabile che non
 * è razionale. */
static void param_collect(const Formula *f, int a_name, int x_name) {
    if (failure) return;
    if (f->kind == F_FORALL || f->kind == F_EXISTS || f->kind == F_SOLVE) {
        if (x_name || !numbers_all_reals(&f->numbers)) { fail(PARAM_FORM); return; }
        param_collect(f->a, a_name, f->variable);
        return;
    }
    if (f->kind != F_EQUAL && f->kind != F_DISTINCT && f->kind != F_LESS && f->kind != F_LESS_EQ) {
        param_collect(f->a, a_name, x_name);
        if (f->b) param_collect(f->b, a_name, x_name);
        return;
    }
    int a = atom_var(a_name);
    if (!x_name || (!node_uses_letter(f->left, x_name) && !node_uses_letter(f->right, x_name))) { sign_prepare(f, a); return; }
    if (!term_is_rational(f->left) || !term_is_rational(f->right)) { fail(PARAM_SHAPE); return; }

    /* Il conto, con le due lettere libere e l'elenco dei divisori acceso. */
    int x = atom_var(x_name);
    condition_count = conditions_lost = undefined = 0;
    env_count = 0;
    conditions_on = 1;
    Rat d = rat_add(eval(f->left), eval(f->right), 1);
    conditions_on = 0;

    /* Una divisione per un'espressione che è zero ovunque: il confronto non
     * ha valore per nessuna coppia di numeri, quindi è sempre falso e non
     * ha polinomi da dare. */
    if (failure && undefined) { failure = NULL; undefined = 0; return; }
    if (conditions_lost) fail("troppe condizioni di esistenza in un confronto");
    if (failure) return;
    param_add(d.num, a, x);
    param_add(d.den, a, x);
    for (int i = 0; i < condition_count && !failure; i++)
        for (int j = 0; j < conditions[i].count; j++) param_add(conditions[i].factor[j], a, x);
}

/* La matrice di cui subresultant_lead() calcola il determinante: minor_size
 * righe e colonne di polinomi nel parametro. */
static Poly minor_entry[MAX_MINOR][MAX_MINOR];
static int minor_size;

/* Ritorna il determinante della matrice fatta dalle righe di minor_entry[]
 * da `row` in giù e dalle colonne non ancora usate, quelle con il bit a zero
 * in `used`.
 *
 * Sviluppo di Laplace lungo la prima riga: la somma, sulle colonne libere c,
 * dell'elemento della riga in c per il determinante di ciò che resta tolte
 * la riga e la colonna, con il segno più se c è la prima, la terza, ...
 * delle colonne libere e meno altrimenti. Gli elementi nulli si saltano: le
 * matrici di subresultant_lead() sono quasi vuote, e così i prodotti da
 * calcolare sono pochi anche con otto righe. */
static Poly minor_determinant(int row, unsigned used) {
    if (row == minor_size) return poly_const(num_int(1));
    Poly sum = {0, NULL};
    for (int c = 0, place = 0; c < minor_size && !failure; c++) {
        if (used >> c & 1) continue;
        if (minor_entry[row][c].count) sum = poly_add(sum, poly_mul(minor_entry[row][c], minor_determinant(row + 1, used | 1u << c)), place % 2);
        place++;
    }
    return sum;
}

/* Ritorna psc_k(f, g), il coefficiente principale del sottorisultante numero
 * k di f e g: polinomi nella variabile di grado m e n, con i coefficienti
 * f[0..m] e g[0..n] che sono polinomi nel parametro, e 0 <= k <= min(m, n).
 * Annota un errore se la matrice ha più di MAX_MINOR righe.
 *
 * Che cos'è. Si scrivono in righe i coefficienti, dalla potenza più alta
 * x^(m+n-k-1) in giù, dei polinomi
 *
 *     x^(n-k-1) f, ..., x f, f, x^(m-k-1) g, ..., x g, g:
 *
 * sono m + n - 2k righe. psc_k è il determinante delle prime m + n - 2k
 * colonne. Con k = 0 è la matrice di Sylvester, e psc_0 il risultante.
 *
 * A che cosa serve. Dove i coefficienti direttivi di f e di g non sono zero,
 * il grado del massimo comun divisore di f e g è il più piccolo k per cui
 * psc_k non è zero. Per k = 0 è il fatto noto che il risultante si annulla
 * esattamente quando f e g hanno una radice in comune: una combinazione
 * u f + v g = 0 con u di grado minore di n e v di grado minore di m è una
 * relazione tra le righe. Per k qualsiasi la stessa matrice dice se esistono
 * u e v, di gradi minori di n - k e m - k, con u f + v g di grado minore di
 * k: succede esattamente quando il massimo comun divisore ha grado più di k
 * (teorema fondamentale dei sottorisultanti; Collins 1975, teorema 2). */
static Poly subresultant_lead(const Poly *f, int m, const Poly *g, int n, int k) {
    minor_size = m + n - 2 * k;
    if (minor_size > MAX_MINOR) { fail(PARAM_DEGREE); return (Poly){0, NULL}; }
    for (int r = 0; r < minor_size; r++) {
        /* Le prime n - k righe sono x^s f con s = n - k - 1, ..., 0; le
         * altre x^s g con s = m - k - 1, ..., 0. */
        int upper = r < n - k, shift = upper ? n - k - 1 - r : m - k - 1 - (r - (n - k));
        for (int c = 0; c < minor_size; c++) {
            /* La colonna c è la potenza x^(m+n-k-1-c), e il suo coefficiente
             * in x^s f è quello di x^(m+n-k-1-c-s) in f. */
            int power = m + n - k - 1 - c - shift;
            minor_entry[r][c] = power < 0 || power > (upper ? m : n) ? (Poly){0, NULL} : upper ? f[power] : g[power];
        }
    }
    return minor_determinant(0, 0);
}

/* Un polinomio della proiezione (18t-a) con la sua provenienza, come
 * param_project() lo ha calcolato: è il dato che 18t-h ricontrolla con un
 * altro conto. Gli elementi si registrano nell'ordine in cui si calcolano,
 * anche quelli che sono un numero o il polinomio nullo. */
typedef struct {
    int kind;    /* 1: il coefficiente direttivo di f (a1); 2: psc_k(f, f')
                    (a2); 3: psc_k(f, g) (a3) */
    int first;   /* il posto di f in param_poly[] */
    int second;  /* a3: il posto di g in param_poly[]; -1 altrimenti */
    int k;       /* a2, a3: il numero del sottorisultante; 0 per a1 */
    Uni value;   /* il polinomio nel parametro, moltiplicato per un intero
                    positivo (uni_from_poly()): ha le stesse radici. Il
                    polinomio nullo se param_first() lo ha trovato nullo */
} ProjectionItem;

/* I polinomi della proiezione dell'enunciato in corso, registrati da
 * param_column(). */
static ProjectionItem param_item[MAX_PROJECTION];
static int param_items;

/* Registra il polinomio p, che è nel solo parametro (atomo a), con la sua
 * provenienza (kind, first, second, k: come in ProjectionItem), e lo mette
 * tra le colonne della tabella nella lettera del parametro: le sue radici
 * sono valori critici. Un numero non ne ha, e tra le colonne non entra; ma
 * si registra, come il polinomio nullo, perché 18t-h veda tutto ciò che la
 * proiezione ha calcolato. */
static void param_column(Poly p, int a, int kind, int first, int second, int k) {
    Uni column;
    int shift;
    if (failure) return;
    if (!uni_from_poly(p, a, &column, &shift) || shift) { fail(PARAM_DEGREE); return; }
    if (param_items == MAX_PROJECTION) { fail("troppi polinomi nella proiezione del parametro"); return; }
    param_item[param_items++] = (ProjectionItem){kind, first, second, k, column};
    if (column.degree > 0) sign_column(column);
}

/* 18t-a2, 18t-a3. Mette tra le colonne il primo psc_k(f, g), k = 0, 1, ...,
 * che non è il polinomio nullo, e registra con lui quelli nulli che lo
 * precedono; kind, first e second dicono da dove vengono f e g, come in
 * ProjectionItem. Se sono tutti nulli fino a min(m, n) - 1, il massimo comun
 * divisore ha grado min(m, n) dovunque i coefficienti direttivi non si
 * annullano, e non c'è nulla da aggiungere. La memoria di ogni determinante
 * torna all'arena appena il polinomio è tra le colonne e tra i registrati,
 * che ne tengono una copia. */
static void param_first(const Poly *f, int m, const Poly *g, int n, int a, int kind, int first, int second) {
    for (int k = 0; k < (m < n ? m : n) && !failure; k++) {
        size_t before = arena_used;
        Poly lead = subresultant_lead(f, m, g, n, k);
        int zero = lead.count == 0;
        param_column(lead, a, kind, first, second, k);
        arena_used = before;
        if (!zero) return;
    }
}

/* 18t-a. La proiezione dei polinomi di param_poly[]: riempie param_part[] e
 * param_degree[], e mette tra le colonne della tabella nella lettera del
 * parametro (atomo a) i polinomi a1, a2 e a3, registrandoli in param_item[].
 * Le coppie si fanno solo tra polinomi nella stessa variabile: radici in
 * variabili diverse non hanno un ordine da conservare.
 *
 * Warning: projection_sound() (18t-h) ricava da sé quali polinomi la
 * proiezione deve contenere, con le stesse regole a1, a2 e a3. Se cambi le
 * regole qui, cambiale anche lì, o il ricontrollo fermerà ogni verdetto (un
 * polinomio che manca) oppure non vedrà ciò che hai aggiunto. */
static void param_project(int a) {
    for (int i = 0; i < param_polys && !failure; i++) {
        param_degree[i] = poly_split(param_poly[i], param_var[i], param_part[i], MAX_PARAM_DEGREE);
        if (param_degree[i] < 0) fail(PARAM_DEGREE);
    }
    for (int i = 0; i < param_polys && !failure; i++) {
        const Poly *f = param_part[i];
        Poly derivative[MAX_PARAM_DEGREE + 1];
        int m = param_degree[i];
        param_column(f[m], a, 1, i, -1, 0);
        for (int j = 1; j <= m; j++) derivative[j - 1] = poly_mul(f[j], poly_const(num_int(j)));
        param_first(f, m, derivative, m - 1, a, 2, i, -1);
        for (int j = i + 1; j < param_polys; j++)
            if (param_var[j] == param_var[i]) param_first(f, m, param_part[j], param_degree[j], a, 3, i, j);
    }
}

/* Un valore critico del parametro: la copia di un punto della tabella dei
 * segni nella lettera del parametro, fatta prima che le decisioni sulle
 * celle riusino quella tabella. */
typedef struct {
    Critical at;    /* il punto: il razionale at.low, oppure la sola radice di
                       `element` tra at.low e at.high (at.element non vale più) */
    Uni element;    /* punto irrazionale: il polinomio di secondo grado, senza
                       radici razionali, di cui è radice */
    int smaller;    /* punto irrazionale: 1 se è la più piccola delle due radici */
    char text[96];  /* com'è scritto, in LaTeX */
} ParamPoint;

/* Una cella della retta del parametro (18t-b). La cella 2 i è l'intervallo
 * prima del valore critico i, la cella 2 i + 1 quel valore; l'ultima è
 * l'intervallo dopo l'ultimo valore critico: come le righe di una tabella
 * dei segni. */
typedef struct {
    Wide sample;           /* il razionale in cui si decide la cella: il punto,
                              o un valore dell'intervallo. Non vale per un
                              punto irrazionale */
    Node *value;           /* il valore della cella come espressione, da
                              scrivere al posto del parametro; sta nell'arena */
    int truth;             /* verifiche e valori del parametro: 1 se nella cella
                              la condizione vale */
    int kind;              /* soluzioni con il parametro: 0 se nella cella non
                              ci sono soluzioni, 2 se lo è ogni x, 1 se sono
                              quelle scritte in text */
    char text[CELL_TEXT];  /* kind == 1: le soluzioni nella variabile, in LaTeX */
} ParamCell;

/* I valori critici e le celle dell'enunciato in corso, riempiti da
 * param_cells_build(). */
static ParamPoint param_point[MAX_PARAM_POINTS];
static int param_points;
static ParamCell param_cell[2 * MAX_PARAM_POINTS + 1];
static int param_cells;

/* Ritorna, come espressione, una radice del polinomio di secondo grado q,
 * che ha due radici reali irrazionali e coefficienti sotto 2^30 (lo ha già
 * controllato quadratic_latex()): la più piccola se smaller è 1. È la
 * formula risolutiva, (-b -+ sqrt(b^2 - 4ac)) / 2a, con il denominatore reso
 * positivo come in quadratic_latex(): così il segno meno dà la più piccola. */
static Node *quadratic_node(const Uni *q, int smaller) {
    long long a = (long long)q->c[2], b = (long long)q->c[1], c = (long long)q->c[0];
    Node *root = node_call(FN_ROOT, node_num(b * b - 4 * a * c), node_num(2));
    return node_new(N_DIV, node_new(smaller ? N_SUB : N_ADD, node_integer(a < 0 ? b : -b), root), node_num(a < 0 ? -2 * a : 2 * a));
}

/* 18t-b. Trova i valori critici del parametro di nome name, dalle colonne
 * già preparate, e riempie param_point[] e param_cell[]. Annota un errore
 * se sono troppi, o se uno è irrazionale e non ha una scrittura con una
 * radice quadrata: lì la cella non si saprebbe decidere. */
static void param_cells_build(int name) {
    sign_points(-1);
    if (!failure && sign_points_count > MAX_PARAM_POINTS) fail("troppi valori critici del parametro");
    if (failure) return;
    param_points = sign_points_count;
    param_cells = 2 * param_points + 1;
    for (int k = 0; k < param_points; k++) {
        ParamPoint *p = &param_point[k];
        p->at = sign_point[k];
        p->text[0] = solution_note[0] = '\0';
        point_latex(k, name, p->text, sizeof p->text);
        if (failure || p->at.exact) continue;
        if (p->at.element < 0 || solution_note[0]) { fail(PARAM_ROOT); return; }

        /* La più piccola delle due radici è il primo dei due punti di
         * questo elemento, come in point_latex(). */
        p->element = sign_base[p->at.element];
        p->smaller = point_is_first_root(k);
    }

    /* Il valore di ogni cella. Per un intervallo è scelto come in
     * sign_table() (interval_sample()): tra i due punti che lo chiudono,
     * oppure un intero oltre l'unico che c'è. */
    for (int c = 0; c < param_cells && !failure; c++) {
        ParamCell *cell = &param_cell[c];
        const ParamPoint *point = c % 2 ? &param_point[c / 2] : NULL;
        const ParamPoint *before = c >= 2 ? &param_point[c / 2 - 1] : NULL, *after = c / 2 < param_points ? &param_point[c / 2] : NULL;
        cell->sample = (Wide){0, 1};
        if (point && !point->at.exact) { cell->value = quadratic_node(&point->element, point->smaller); continue; }
        cell->sample = point ? point->at.low : interval_sample(before ? &before->at : NULL, after ? &after->at : NULL);
        cell->value = node_rational(cell->sample);
    }
}

/* Ritorna il numero della cella in cui cade il razionale v. Rispetto a un
 * valore critico irrazionale, v sta a sinistra se non supera l'estremo
 * inferiore dell'intervallo che lo isola, a destra se non sta sotto quello
 * superiore; dentro l'intervallo lo dice il segno del polinomio, che lì ha
 * quella sola radice, semplice: a sinistra della radice ha il segno che ha
 * nell'estremo inferiore. */
static int param_cell_of(Wide v) {
    for (int k = 0; k < param_points; k++) {
        const ParamPoint *p = &param_point[k];
        int side;
        if (p->at.exact) side = wide_cmp(v, p->at.low);
        else if (wide_cmp(v, p->at.low) <= 0) side = -1;
        else if (wide_cmp(v, p->at.high) >= 0) side = 1;
        else side = uni_sign_at(&p->element, v) == uni_sign_at(&p->element, p->at.low) ? -1 : 1;
        if (side <= 0) return side < 0 ? 2 * k : 2 * k + 1;
    }
    return 2 * param_points;
}

/* Ritorna un altro razionale dell'intervallo che è la cella c, oltre a
 * quello scelto: a destra del valore scelto se right è 1, a sinistra
 * altrimenti (18t-f). */
static Wide cell_beside(int c, int right) {
    const ParamPoint *before = c >= 2 ? &param_point[c / 2 - 1] : NULL, *after = c / 2 < param_points ? &param_point[c / 2] : NULL;
    Wide sample = param_cell[c].sample;
    if (right) return after ? wide_between(sample, after->at.low) : wide_add(sample, (Wide){1, 1});
    return before ? wide_between(before->at.high, sample) : wide_add(sample, (Wide){-1, 1});
}

/* =============================================================================
 * 18.18 UN PARAMETRO: LE CELLE DECISE E SCRITTE
 * ============================================================================
 *
 * Una cella alla volta: con il suo valore al posto del parametro l'enunciato
 * ha una variabile sola, e lo decide la tabella dei segni (18t-c,
 * table_truth(), closed_truth()). Poi ciò che si scrive: le condizioni sul
 * parametro che dicono "in queste celle" (18t-d), e le soluzioni in x con
 * gli estremi in funzione del parametro, riconosciuti tra i candidati che
 * danno le formule di primo e di secondo grado (18t-e).
 */

/* Il controesempio dell'ultimo enunciato che table_truth() ha trovato falso,
 * com'è scritto da decide_by_signs(); vuoto se non ne ha dato uno. */
static char param_inner[160];

/* Decide con la tabella dei segni (18p) l'enunciato q: un quantificatore su
 * una variabile reale, con una condizione senza altri quantificatori.
 * Ritorna 1 se è vero, 0 se è falso; -1 se la tabella non lo decide, e
 * allora mette in *verdict il suo esito e il suo motivo, che non è mai
 * NULL. Lascia in param_inner il controesempio, se ce n'è uno.
 *
 * Il testo che decide_by_signs() aggiunge alla dimostrazione viene tolto:
 * la dimostrazione di questa regola dice che cosa succede in ogni cella,
 * non come 18p lo ha trovato. */
static int table_truth(const Formula *q, Verdict *verdict) {
    Verdict inner = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    size_t opening = proof_length;
    param_inner[0] = '\0';

    /* Un errore già annotato, come la memoria finita mentre si copiava
     * l'enunciato, va guardato qui: decide_by_signs() riparte da capo, lo
     * cancellerebbe e deciderebbe un enunciato copiato a metà. */
    if (failure) {
        verdict->outcome = UNSUPPORTED;
        verdict->reason = failure;
        failure = NULL;
        return -1;
    }
    decide_by_signs(q, &inner);
    proof_cut(opening);
    if (inner.outcome == REFUTED && inner.detail) snprintf(param_inner, sizeof param_inner, "%s", inner.detail);
    if (inner.outcome == PROVED || inner.outcome == REFUTED) return inner.outcome == PROVED;
    verdict->outcome = inner.outcome;
    verdict->reason = inner.reason ? inner.reason : PARAM_INNER;
    return -1;
}

/* Decide il confronto tra numeri f, come table_truth(): lo mette sotto un
 * "per ogni" di comodo, la cui lettera è quella del parametro, name, che
 * dopo la sostituzione non compare più. Il "controesempio" di un confronto
 * tra numeri non dice nulla, e non resta in param_inner. */
static int number_truth(Formula *f, int name, Verdict *verdict) {
    Formula all;
    memset(&all, 0, sizeof all);
    all.kind = F_FORALL;
    all.a = f;
    all.variable = name;
    all.numbers.reals = 1;
    int truth = table_truth(&all, verdict);
    param_inner[0] = '\0';
    return truth;
}

/* Le due condizioni costanti di closed_reduce(): la falsa e la vera. Si
 * riconoscono dall'indirizzo e non hanno contenuto: non arrivano mai a una
 * tabella dei segni. */
static Formula closed_constant[2];

/* Ritorna la negazione della condizione f, che può essere una delle due
 * costanti. */
static Formula *closed_not(Formula *f) {
    if (f == &closed_constant[0] || f == &closed_constant[1]) return &closed_constant[f == &closed_constant[0]];
    return formula_node(F_NOT, f, NULL, f->start);
}

/* Semplifica la condizione f, senza quantificatori, in cui il parametro di
 * nome name è già sostituito da un numero e la sola lettera rimasta è la
 * variabile x_name: ogni confronto senza la variabile è un confronto tra
 * numeri, lo si decide subito (number_truth()) e lo si toglie, con le
 * regole dei connettivi ("falso e A" è falso, "vero e A" è A, ...). Ritorna
 * la condizione che resta, in cui ogni confronto contiene la variabile,
 * oppure una delle due costanti; NULL se un confronto tra numeri non si
 * riesce a decidere, con l'esito e il motivo in *verdict.
 *
 * A che cosa serve. Un elenco di casi sul parametro, come quello che questa
 * regola scrive, è fatto per lo più di confronti nel solo parametro: con il
 * parametro uguale a un numero resta in piedi un caso solo. Senza questo
 * passo la tabella dei segni li riceverebbe tutti, e un elenco di sette
 * casi supera da solo il numero di confronti che una tabella tiene
 * (MAX_SIGN_ATOMS): è successo, e le soluzioni giuste di una richiesta con
 * due condizioni non si lasciavano rileggere. */
static Formula *closed_reduce(Formula *f, int x_name, int name, Verdict *verdict) {
    Formula *no = &closed_constant[0], *yes = &closed_constant[1];
    if (f->kind == F_EQUAL || f->kind == F_DISTINCT || f->kind == F_LESS || f->kind == F_LESS_EQ) {
        if (node_uses_letter(f->left, x_name) || node_uses_letter(f->right, x_name)) return f;
        int truth = number_truth(f, name, verdict);
        return truth < 0 ? NULL : truth ? yes : no;
    }
    Formula *a = closed_reduce(f->a, x_name, name, verdict), *b = a && f->b ? closed_reduce(f->b, x_name, name, verdict) : NULL;
    if (!a || (f->b && !b)) return NULL;
    switch (f->kind) {
    case F_NOT:
        return a == f->a ? f : closed_not(a);
    case F_AND:
        if (a == no || b == no) return no;
        if (a == yes || b == yes) return a == yes ? b : a;
        break;
    case F_OR:
        if (a == yes || b == yes) return yes;
        if (a == no || b == no) return a == no ? b : a;
        break;
    case F_IMPLIES:
        if (a == no || b == yes) return yes;
        if (a == yes) return b;
        if (b == no) return closed_not(a);
        break;
    default:
        /* "Se e solo se": con un lato vero è l'altro, con un lato falso la
         * sua negazione. */
        if (a == yes || b == yes) return a == yes ? b : a;
        if (a == no || b == no) return closed_not(a == no ? b : a);
        break;
    }
    return a == f->a && b == f->b ? f : formula_node(f->kind, a, b, f->start);
}

/* 18t-c. Decide l'enunciato f, in cui il parametro di nome name è già
 * sostituito da un numero: una combinazione di confronti tra numeri e di
 * enunciati "per ogni x" o "esiste x". Ritorna 1 se è vero, 0 se è falso;
 * -1 se la tabella dei segni non lo decide, e allora mette in *verdict il
 * suo esito e il suo motivo.
 *
 * I connettivi si calcolano dalle parti. Un confronto tra numeri e un
 * quantificatore li decide 18p; della condizione di un quantificatore si
 * tolgono prima i confronti tra numeri (closed_reduce()), e se non resta
 * altro la sua verità è quella della costante rimasta, perché la variabile
 * varia su un insieme che non è vuoto. */
static int closed_truth(Formula *f, int name, Verdict *verdict) {
    if (f->kind == F_NOT) {
        int inner = closed_truth(f->a, name, verdict);
        return inner < 0 ? -1 : !inner;
    }
    if (f->kind == F_AND || f->kind == F_OR || f->kind == F_IMPLIES || f->kind == F_IFF) {
        int a = closed_truth(f->a, name, verdict), b = a < 0 ? -1 : closed_truth(f->b, name, verdict);
        if (b < 0) return -1;
        return f->kind == F_AND ? a && b : f->kind == F_OR ? a || b : f->kind == F_IMPLIES ? !a || b : a == b;
    }
    if (f->kind != F_FORALL && f->kind != F_EXISTS) return number_truth(f, name, verdict);
    Formula reduced = *f;
    reduced.a = closed_reduce(f->a, f->variable, name, verdict);
    if (!reduced.a) return -1;
    if (reduced.a == &closed_constant[0] || reduced.a == &closed_constant[1]) {
        param_inner[0] = '\0';
        return reduced.a == &closed_constant[1];
    }
    return table_truth(&reduced, verdict);
}

/* Aggiunge a text, di size byte, un pezzo di un insieme di numeri nella
 * lettera name, con le convenzioni di sign_solution(): un intervallo tra gli
 * estremi scritti in low e high, una semiretta se uno dei due è NULL, un
 * punto solo se low e high sono lo stesso puntatore. low_closed e
 * high_closed dicono se l'estremo è compreso. I due non sono mai NULL
 * insieme: "ogni numero" non è un pezzo, e chi chiama lo scrive da sé. */
static void piece_latex(char *text, size_t size, int name, const char *low, int low_closed, const char *high, int high_closed) {
    if (low == high) text_add(text, size, "%c = %s", name, low);
    else if (!low) text_add(text, size, "%c %s %s", name, high_closed ? "\\le" : "<", high);
    else if (!high) text_add(text, size, "%c %s %s", name, low_closed ? "\\ge" : ">", low);
    else text_add(text, size, "%s %s %c %s %s", low, low_closed ? "\\le" : "<", name, high_closed ? "\\le" : "<", high);
}

/* 18t-d. Aggiunge a text, di size byte, la condizione sul parametro di nome
 * name che dice "in una delle celle da first a last", che sono consecutive
 * e non sono tutte. Una cella dispari è un punto, quindi un tratto che
 * comincia o finisce lì lo comprende; se comincia o finisce su un
 * intervallo, il punto accanto resta fuori. */
static void cells_latex(int first, int last, int name, char *text, size_t size) {
    const char *low = first == 0 ? NULL : param_point[first % 2 ? first / 2 : first / 2 - 1].text;
    const char *high = last == param_cells - 1 ? NULL : param_point[last / 2].text;
    piece_latex(text, size, name, low, first % 2, high, last % 2);
}

/* Scrive nella dimostrazione di quale cella si parla: il valore critico,
 * oppure l'intervallo con il razionale scelto al suo interno. */
static void put_cell(int c, int name) {
    if (c % 2) { proof_add("$%c = %s$", name, param_point[c / 2].text); return; }
    proof_add("$");
    if (c >= 2) proof_add("%s < ", param_point[c / 2 - 1].text);
    proof_add("%c", name);
    if (c / 2 < param_points) proof_add(" < %s", param_point[c / 2].text);
    proof_add("$ (for instance $%c = ", name);
    put_wide(param_cell[c].sample);
    proof_add("$)");
}

/* Un estremo delle soluzioni scritto in funzione del parametro (18t-e): vale
 *
 *     (top + sigma * outside * sqrt(radicand)) / bottom,
 *
 * dove top, radicand e bottom sono polinomi nel parametro a coefficienti
 * interi. Invariante: bottom non è il polinomio nullo e ha il coefficiente
 * direttivo positivo; se sigma è 0 la radice non c'è, e outside e radicand
 * non contano; altrimenti outside è positivo. */
typedef struct {
    Uni top, bottom, radicand;
    int sigma;          /* 0, oppure il segno davanti alla radice: 1 o -1 */
    long long outside;  /* il numero intero davanti alla radice */
} Candidate;

/* I candidati dell'enunciato in corso, riempiti da candidates_build(). */
static Candidate param_candidate[MAX_CANDIDATES];
static int param_candidates;

/* Ritorna p moltiplicato per l'intero k. */
Uni uni_scaled(const Uni *p, __int128 k) {
    Uni out = *p;
    for (int i = 0; i <= out.degree; i++)
        if (__builtin_mul_overflow(out.c[i], k, &out.c[i])) fail(SIGN_LIMIT);
    uni_trim(&out);
    return out;
}

/* Ritorna il valore di p nel razionale x: lo schema di Horner, con le
 * frazioni a 128 bit. */
static Wide uni_value(const Uni *p, Wide x) {
    Wide value = {0, 1};
    for (int i = p->degree; i >= 0 && !failure; i--) value = wide_add(wide_mul(value, x), (Wide){p->c[i], 1});
    return value;
}

/* Scrive il polinomio p, che è nel solo atomo a con coefficienti razionali,
 * come content per *out: *out a coefficienti interi senza divisori comuni e
 * con il coefficiente direttivo positivo, content razionale. Il polinomio
 * nullo dà *out nullo e content zero. Ritorna 0, annotando un errore, se p
 * non ha questa forma o se i numeri sono troppo grandi.
 *
 * uni_from_poly() dà già un multiplo intero di p; il rapporto tra p e *out
 * si legge poi su un coefficiente solo, quello di grado più alto. */
static int uni_exact(Poly p, int a, Uni *out, Wide *content) {
    int shift;
    *content = (Wide){0, 1};
    if (!uni_from_poly(p, a, out, &shift) || shift) { fail(PARAM_DEGREE); return 0; }
    if (out->degree < 0) return 1;
    uni_primitive(out);
    if (out->c[out->degree] < 0) uni_negate(out);
    for (int t = 0; t < p.count; t++) {
        const Term *term = &p.term[t];
        __int128 below;
        if ((term->mono.count ? term->mono.factor[0].exp.num : 0) != out->degree) continue;
        if (__builtin_mul_overflow(out->c[out->degree], (__int128)term->coef.re.den, &below)) { fail(SIGN_LIMIT); return 0; }
        *content = wide_make(term->coef.re.num, below);
    }
    return 1;
}

/* Ritorna il polinomio scale per u nell'atomo a. */
static Poly poly_from_uni(const Uni *u, int a, Frac scale) {
    Poly p = {0, NULL};
    for (int i = 0; i <= u->degree && !failure; i++) {
        Term term;
        if (u->c[i] == 0) continue;
        term.coef = num_frac(frac_mul(scale, frac_make(u->c[i], 1)));
        term.mono.count = 0;
        if (i > 0) term.mono = mono_atom(a, frac_int(i));
        p = poly_add(p, poly_term(term), 0);
    }
    return p;
}

/* Cerca il polinomio a coefficienti interi di cui p è il quadrato: se i
 * conti tornano lo mette in *root, con il coefficiente direttivo positivo, e
 * ritorna 1. Il polinomio nullo è il quadrato di se stesso.
 *
 * Se p = r^2 con r di grado e, il coefficiente di grado e + i di p è
 *
 *     2 r_e r_i + (la somma degli r_j r_{e+i-j} con i < j < e),
 *
 * in cui oltre a r_i compaiono solo coefficienti di r più alti. Quindi r_e è
 * la radice del coefficiente direttivo, e scendendo ogni r_i si ricava con
 * una divisione, che deve essere esatta. I coefficienti di p sotto il grado
 * e qui non vengono guardati: un "sì" va confermato da chi chiama,
 * moltiplicando. */
static int uni_square_root(const Uni *p, Uni *root) {
    int e = p->degree / 2;
    root->degree = p->degree < 0 ? -1 : e;
    memset(root->c, 0, sizeof root->c);
    if (p->degree < 0) return 1;
    if (p->degree % 2 || p->c[p->degree] < 0 || p->c[p->degree] >= (__int128)1 << 126) return 0;
    root->c[e] = wide_isqrt(p->c[p->degree]);
    if (root->c[e] * root->c[e] != p->c[p->degree]) return 0;
    for (int i = e - 1; i >= 0; i--) {
        __int128 rest = p->c[e + i], part;
        for (int j = i + 1; j < e; j++)
            if (__builtin_mul_overflow(root->c[j], root->c[e + i - j], &part) || __builtin_sub_overflow(rest, part, &rest)) return 0;
        if (rest % (2 * root->c[e]) != 0) return 0;
        root->c[i] = rest / (2 * root->c[e]);
    }
    return 1;
}

/* Aggiunge c ai candidati, se non c'è già: due polinomi diversi possono
 * avere una radice in comune, e allora la stessa formula nasce due volte. */
static void candidate_add(const Candidate *c) {
    for (int i = 0; i < param_candidates; i++) {
        const Candidate *other = &param_candidate[i];
        if (other->sigma != c->sigma || !uni_equal(&other->top, &c->top) || !uni_equal(&other->bottom, &c->bottom)) continue;
        if (!c->sigma || (other->outside == c->outside && uni_equal(&other->radicand, &c->radicand))) return;
    }
    if (param_candidates == MAX_CANDIDATES) { fail(PARAM_WRITE); return; }
    param_candidate[param_candidates++] = *c;
}

/* Aggiunge ai candidati la frazione num / den di polinomi nel parametro
 * (atomo a), ridotta ai minimi termini: così due scritture della stessa
 * funzione sono lo stesso candidato, e (4a + 4a) / 2 si legge 4a. den non è
 * il polinomio nullo. */
static void candidate_ratio(Poly num, Poly den, int a) {
    Candidate c;
    Uni top, bottom, common, rest;
    Wide above, below;
    memset(&c, 0, sizeof c);
    c.radicand.degree = -1;
    if (!uni_exact(num, a, &top, &above) || !uni_exact(den, a, &bottom, &below)) return;
    if (top.degree < 0) {
        /* Zero, qualunque sia il denominatore. */
        c.top = top;
        c.bottom = (Uni){0, {1}};
    } else {
        common = uni_gcd(top, bottom);
        if (failure || !uni_divide(&top, &common, &rest)) { fail(SIGN_LIMIT); return; }
        top = rest;
        if (!uni_divide(&bottom, &common, &rest)) { fail(SIGN_LIMIT); return; }

        /* Il numero che resta davanti, above / below, va sopra con il suo
         * numeratore e sotto con il suo denominatore, che è positivo. */
        Wide ratio = wide_mul(above, wide_make(below.den, below.num));
        c.top = uni_scaled(&top, ratio.num);
        c.bottom = uni_scaled(&rest, ratio.den);
    }
    if (!failure) candidate_add(&c);
}

/* Aggiunge ai candidati (minus_b + sigma sqrt(D)) / two_a, una radice di un
 * polinomio di secondo grado in x il cui discriminante D = content per
 * *primitive non è il quadrato di un polinomio. minus_b e two_a sono
 * polinomi nel parametro (atomo a), e two_a non è nullo.
 *
 * Perché la scrittura sia quella dei libri, 2 - \sqrt{4 - k^{2}} e non
 * \frac{4 - \sqrt{16 - 4k^{2}}}{2}, da sotto la radice si porta fuori ciò
 * che si può del numero content, e i tre numeri che restano davanti a
 * minus_b, alla radice e a two_a si riducono a interi senza divisori
 * comuni. */
static void candidate_radical(Poly minus_b, Poly two_a, const Uni *primitive, Wide content, int sigma, int a) {
    Candidate c;
    Uni top, bottom;
    Wide above, below;
    if (!uni_exact(minus_b, a, &top, &above) || !uni_exact(two_a, a, &bottom, &below)) return;

    /* sqrt(|content|) = outside sqrt(inside) / q, dove |content| = p / q:
     * infatti p / q = p q / q^2, e da p q si portano fuori i quadrati. */
    __int128 inside;
    if (__builtin_mul_overflow(content.num < 0 ? -content.num : content.num, content.den, &inside)) { fail(SIGN_LIMIT); return; }
    __int128 outside = square_out(&inside);

    /* I tre numeri, moltiplicati per il prodotto dei loro denominatori. */
    Wide scale = wide_mul(wide_mul((Wide){above.den, 1}, (Wide){below.den, 1}), (Wide){content.den, 1});
    __int128 over = wide_mul(above, scale).num, beside = wide_mul(wide_make(outside, content.den), scale).num, under = wide_mul(below, scale).num;
    if (failure) return;
    __int128 common = gcd128(gcd128(over, beside), under);
    if (under < 0) { over = -over; under = -under; sigma = -sigma; }
    if (beside / common >= COEF_LIMIT) { fail(SIGN_LIMIT); return; }
    c.top = uni_scaled(&top, over / common);
    c.bottom = uni_scaled(&bottom, under / common);
    c.radicand = uni_scaled(primitive, content.num < 0 ? -inside : inside);
    c.sigma = sigma;
    c.outside = (long long)(beside / common);
    if (!failure) candidate_add(&c);
}

/* 18t-e. Riempie param_candidate[] con le radici, scritte in funzione del
 * parametro (atomo a), dei polinomi di param_poly[] di primo e di secondo
 * grado nella variabile di atomo x. Va chiamata dopo param_project().
 *
 *   - c_1 x + c_0 ha la radice -c_0 / c_1.
 *   - A x^2 + B x + C ha le radici (-B +- sqrt(D)) / 2A, con D = B^2 - 4AC.
 *     Se D è il quadrato di un polinomio E le radici sono (-B +- E) / 2A,
 *     senza radicali: è il caso di quasi tutti gli esercizi, dove il
 *     trinomio è un prodotto come (x - a)(a x + 3). Che D sia E^2 si
 *     controlla moltiplicando.
 *
 * Le radici dei polinomi di grado più alto non hanno candidati: se un
 * estremo delle soluzioni è una di loro, la regola rinuncia. */
static void candidates_build(int x, int a) {
    for (int i = 0; i < param_polys && !failure; i++) {
        const Poly *part = param_part[i];
        if (param_var[i] != x) continue;
        if (param_degree[i] == 1) candidate_ratio(poly_negate(part[0]), part[1], a);
        if (param_degree[i] != 2) continue;
        Poly minus_b = poly_negate(part[1]), two_a = poly_mul(part[2], poly_const(num_int(2)));
        Poly d = poly_add(poly_mul(part[1], part[1]), poly_mul(poly_mul(part[2], part[0]), poly_const(num_int(4))), 1);
        Uni primitive, root;
        Wide content;
        if (!uni_exact(d, a, &primitive, &content)) return;

        /* D = content per primitive è un quadrato se lo sono tutti e due:
         * il numero, cioè numeratore e denominatore, e il polinomio. */
        __int128 p = 0, q = 0;
        if (content.num >= 0 && content.num < (__int128)1 << 126 && content.den < (__int128)1 << 62) {
            p = wide_isqrt(content.num);
            q = wide_isqrt(content.den);
        }
        if (p * p == content.num && q * q == content.den && uni_square_root(&primitive, &root)) {
            Poly e = poly_from_uni(&root, a, frac_make(p, q));
            if (!failure && poly_equal(poly_mul(e, e), d)) {
                candidate_ratio(poly_add(minus_b, e, 1), two_a, a);
                candidate_ratio(poly_add(minus_b, e, 0), two_a, a);
                continue;
            }
        }
        candidate_radical(minus_b, two_a, &primitive, content, -1, a);
        candidate_radical(minus_b, two_a, &primitive, content, 1, a);
    }
}

/* Ritorna 1 se il candidato c, quando il parametro vale il razionale at, è
 * il punto `point` di una tabella dei segni nella variabile: il razionale
 * point->low, oppure la sola radice di *element tra point->low e
 * point->high (element è NULL per un punto razionale). Il confronto è
 * esatto.
 *
 * Con il parametro uguale a un numero il candidato vale (t + s sqrt(r)) / b,
 * con t, r, b razionali e s = sigma * outside. Se r è il quadrato di un
 * razionale è un razionale, e si confronta con un punto razionale. Se non lo
 * è, è irrazionale: è una delle due radici di
 *
 *     q(x) = (b x - t)^2 - s^2 r,
 *
 * che non ha radici razionali, la più grande se s e b hanno lo stesso segno.
 * È una radice di *element solo se q lo divide, perché q è il polinomio di
 * grado più basso che la annulla; e allora la radice di q nell'intervallo
 * del punto, se c'è, è il punto. C'è se q cambia segno tra i due estremi, ed
 * è la più piccola delle due se nell'estremo inferiore q è positivo: il suo
 * coefficiente direttivo b^2 lo è, e q è positivo prima della radice più
 * piccola. */
static int candidate_is(const Candidate *c, Wide at, const Critical *point, const Uni *element) {
    Wide top = uni_value(&c->top, at), bottom = uni_value(&c->bottom, at), inside = {0, 1};
    if (c->sigma) inside = uni_value(&c->radicand, at);
    if (failure || bottom.num == 0 || inside.num < 0) return 0;
    if (inside.num >= (__int128)1 << 126 || inside.den >= (__int128)1 << 126) { fail(SIGN_LIMIT); return 0; }
    __int128 p = wide_isqrt(inside.num), q = wide_isqrt(inside.den);
    Wide beside = {c->sigma * c->outside, 1};
    if (p * p == inside.num && q * q == inside.den) {
        Wide value = wide_mul(wide_add(top, wide_mul(beside, (Wide){p, q})), wide_make(bottom.den, bottom.num));
        return point->exact && !failure && wide_cmp(value, point->low) == 0;
    }
    if (point->exact) return 0;

    /* I coefficienti di q, portati a interi con il prodotto dei loro
     * denominatori. */
    Wide two = wide_mul(bottom, bottom), one = wide_mul((Wide){-2, 1}, wide_mul(top, bottom));
    Wide zero = wide_add(wide_mul(top, top), wide_mul((Wide){-1, 1}, wide_mul(wide_mul(beside, beside), inside)));
    Wide scale = wide_mul(wide_mul((Wide){two.den, 1}, (Wide){one.den, 1}), (Wide){zero.den, 1});
    Uni quadratic = {2, {wide_mul(zero, scale).num, wide_mul(one, scale).num, wide_mul(two, scale).num}}, rest;
    if (failure) return 0;
    uni_primitive(&quadratic);
    if (!uni_divide(element, &quadratic, &rest)) return 0;
    int low = uni_sign_at(&quadratic, point->low), high = uni_sign_at(&quadratic, point->high);
    if (failure || low * high >= 0) return 0;
    int larger = (c->sigma > 0) == (bottom.num > 0);
    return (low > 0) != larger;
}

/* Aggiunge a text, di size byte, il polinomio p nella lettera name: come
 * uni_latex(), ma dal termine noto in su quando così non comincia con un
 * segno meno. È la scrittura dei libri: 4 - k^{2}, non -k^{2} + 4. */
static void param_poly_latex(const Uni *p, int name, char *text, size_t size) {
    if (p->degree < 1 || p->c[p->degree] > 0 || p->c[0] <= 0) { uni_latex(p, name, text, size); return; }
    for (int i = 0; i <= p->degree; i++) {
        __int128 c = p->c[i], magnitude = c < 0 ? -c : c;
        if (c == 0) continue;
        text_add(text, size, "%s", i == 0 ? "" : c < 0 ? " - " : " + ");
        if (magnitude != 1 || i == 0) text_add(text, size, "%lld", (long long)magnitude);
        if (i > 0) text_add(text, size, "%c", name);
        if (i > 1) text_add(text, size, "^{%d}", i);
    }
}

/* Aggiunge a text, di size byte, il candidato c, in LaTeX, con il parametro
 * di nome name: 4a, -\frac{3}{a}, \frac{a - 1}{2}, 2 - \sqrt{4 - k^{2}}. */
static void candidate_latex(const Candidate *c, int name, char *text, size_t size) {
    char above[256] = "";
    Uni top = c->top;
    int fraction = c->bottom.degree > 0 || c->bottom.c[0] != 1, terms = 0;
    for (int i = 0; i <= top.degree; i++) terms += top.c[i] != 0;

    /* Il segno meno di un numeratore di un solo termine va davanti alla
     * frazione. */
    int minus = fraction && !c->sigma && terms == 1 && top.c[top.degree] < 0;
    if (minus) uni_negate(&top);
    if (terms > 0 || !c->sigma) param_poly_latex(&top, name, above, sizeof above);
    if (c->sigma) {
        text_add(above, sizeof above, "%s", terms > 0 ? (c->sigma > 0 ? " + " : " - ") : c->sigma > 0 ? "" : "-");
        if (c->outside != 1) text_add(above, sizeof above, "%lld", c->outside);
        text_add(above, sizeof above, "\\sqrt{");
        param_poly_latex(&c->radicand, name, above, sizeof above);
        text_add(above, sizeof above, "}");
    }
    if (!fraction) { text_add(text, size, "%s", above); return; }
    text_add(text, size, "%s\\frac{%s}{", minus ? "-" : "", above);
    param_poly_latex(&c->bottom, name, text, size);
    text_add(text, size, "}");
}

/* Aggiunge a text, di size byte, il punto numero k della tabella dei segni
 * nella variabile x_name appena riempita per la cella cell, scritto come
 * estremo delle soluzioni. Ritorna 0 se non lo sa scrivere.
 *
 * In una cella che è un punto (point = 1) il parametro è un numero e
 * l'estremo anche: lo scrive point_latex(). In un intervallo l'estremo è il
 * solo candidato che nel valore scelto coincide con lui: nessuno, o più
 * d'uno, e la regola rinuncia. */
static int endpoint_latex(int k, const ParamCell *cell, int point, int a_name, int x_name, char *text, size_t size) {
    const Critical *end = &sign_point[k];
    int found = -1;
    if (point) {
        solution_note[0] = '\0';
        point_latex(k, x_name, text, size);
        return !solution_note[0];
    }
    if (!end->exact && end->element < 0) return 0;
    for (int i = 0; i < param_candidates && !failure; i++) {
        if (!candidate_is(&param_candidate[i], cell->sample, end, end->exact ? NULL : &sign_base[end->element])) continue;
        if (found >= 0) return 0;
        found = i;
    }
    if (found < 0 || failure) return 0;
    candidate_latex(&param_candidate[found], a_name, text, size);
    return 1;
}

/* 18t-e. Scrive in cell->text e cell->kind le soluzioni nella variabile
 * x_name della condizione body, che ha già il valore della cella al posto
 * del parametro a_name e di cui decide_by_signs() ha appena riempito la
 * tabella. I pezzi sono quelli di sign_solution(); cambia come si scrivono
 * gli estremi (endpoint_latex()). Ritorna 0 se un estremo non si sa
 * scrivere. */
static int cell_solutions(ParamCell *cell, int point, const Formula *body, int a_name, int x_name) {
    Piece piece;
    int pieces = 0;
    cell->text[0] = '\0';
    cell->kind = 1;
    for (int from = 0; !failure && sign_piece(body, from, &piece); from = piece.last + 1) {
        char low[200] = "", high[200] = "";
        int single = piece.first == piece.last && piece.low_closed;
        if (piece.low < 0 && piece.high < 0) { cell->kind = 2; return 1; }
        if (piece.low >= 0 && !endpoint_latex(piece.low, cell, point, a_name, x_name, low, sizeof low)) return 0;
        if (piece.high >= 0 && !single && !endpoint_latex(piece.high, cell, point, a_name, x_name, high, sizeof high)) return 0;
        if (pieces++) text_add(cell->text, sizeof cell->text, " \\lor ");
        piece_latex(cell->text, sizeof cell->text, x_name, piece.low < 0 ? NULL : low, piece.low_closed, single ? low : piece.high < 0 ? NULL : high, piece.high_closed);
    }
    if (!pieces) cell->kind = 0;
    return !failure;
}

/* Ritorna 1 se le celle a e b hanno le stesse soluzioni, scritte allo stesso
 * modo. */
static int cell_same(const ParamCell *a, const ParamCell *b) {
    return a->kind == b->kind && (a->kind != 1 || strcmp(a->text, b->text) == 0);
}

/* 18t-e. Scrive in text, di size byte, le soluzioni con il parametro: un
 * caso per ogni tratto di celle consecutive con le stesse soluzioni, nella
 * forma (condizione sul parametro \land soluzioni in x). Un tratto senza
 * soluzioni non si scrive; di uno in cui ogni x è soluzione si scrive la
 * sola condizione sul parametro; se il tratto sono tutte le celle la
 * condizione sul parametro non serve. Ritorna 1 se il testo è una
 * condizione che si può rileggere, 0 se è una delle due frasi "ogni x" e
 * "nessun x". */
static int param_cases(int a_name, int x_name, char *text, size_t size) {
    int written = 0, total = 0, plain = 1;
    text[0] = '\0';

    /* Quanti casi si scriveranno: uno solo non vuole parentesi. */
    for (int c = 0; c < param_cells; c++)
        total += param_cell[c].kind != 0 && (c == 0 || !cell_same(&param_cell[c], &param_cell[c - 1]));
    for (int first = 0, last; first < param_cells; first = last + 1) {
        const ParamCell *cell = &param_cell[first];
        int whole;
        for (last = first; last + 1 < param_cells && cell_same(&param_cell[last + 1], cell); last++) continue;
        if (cell->kind == 0) continue;
        whole = first == 0 && last == param_cells - 1;
        if (written++) text_add(text, size, " \\lor ");
        if (whole && cell->kind == 2) {
            text_add(text, size, "\\forall %c \\in \\mathbb{R}", x_name);
            plain = 0;
        } else if (whole) {
            text_add(text, size, "%s", cell->text);
        } else if (cell->kind == 2) {
            cells_latex(first, last, a_name, text, size);
        } else {
            int nested = strstr(cell->text, "\\lor") != NULL;
            text_add(text, size, "%s", total > 1 ? "(" : "");
            cells_latex(first, last, a_name, text, size);
            text_add(text, size, " \\land %s%s%s%s", nested ? "(" : "", cell->text, nested ? ")" : "", total > 1 ? ")" : "");
        }
    }
    if (!written) {
        text_add(text, size, "\\nexists %c \\in \\mathbb{R}", x_name);
        plain = 0;
    }
    return plain;
}

/* 18t-d. Scrive in text, di size byte, i valori del parametro di nome name
 * per cui la condizione vale: i tratti di celle consecutive con truth a 1,
 * come sign_solution() scrive i pezzi di una tabella. Ritorna 1 se il testo
 * è una condizione che si può rileggere, 0 se è una delle due frasi "ogni
 * valore" e "nessun valore". */
static int param_values(int name, char *text, size_t size) {
    int pieces = 0;
    text[0] = '\0';
    for (int first = 0, last; first < param_cells; first = last + 1) {
        for (last = first; param_cell[first].truth && last + 1 < param_cells && param_cell[last + 1].truth; last++) continue;
        if (!param_cell[first].truth) continue;
        if (first == 0 && last == param_cells - 1) { text_add(text, size, "\\forall %c \\in \\mathbb{R}", name); return 0; }
        if (pieces++) text_add(text, size, " \\lor ");
        cells_latex(first, last, name, text, size);
    }
    if (!pieces) text_add(text, size, "\\nexists %c \\in \\mathbb{R}", name);
    return pieces > 0;
}

/* =============================================================================
 * 18.19 UN PARAMETRO: I CONTROLLI E IL VERDETTO
 * ============================================================================
 *
 * I tre controlli indipendenti descritti in testa al capitolo 18.17: le
 * soluzioni rilette e riprovate in ogni cella (18t-f), la griglia di valori
 * del parametro scelti senza guardare le celle (18t-g), la proiezione
 * ricalcolata con un altro algoritmo (18t-h). Poi il punto di ingresso della
 * regola, param_decide(), che mette tutto in fila.
 */

/* 18t-f. Controlla che la condizione written dica, del parametro di nome
 * name, ciò che dicono le celle: nel valore di ogni cella, e in altri due
 * razionali di ogni intervallo, written con il numero al posto del parametro
 * deve risultare vera esattamente quando la cella ha truth a 1 (by_cell = 1),
 * oppure vera e basta (by_cell = 0). La decide closed_truth(), cioè la
 * tabella dei segni. Ritorna 1 se tutto concorda; altrimenti 0, con l'esito
 * NOT_PROVED e il motivo in *verdict. */
static int param_reread(const Formula *written, int name, int by_cell, Verdict *verdict) {
    static char reason[400];
    for (int c = 0; c < param_cells; c++)
        for (int i = 0; i < (c % 2 ? 1 : 3); i++) {
            Scratch mark = scratch_mark();
            Formula *closed = formula_with(written, name, i == 0 ? param_cell[c].value : node_rational(cell_beside(c, i == 2)));
            int truth = -1;
            if (failure) { verdict->reason = failure; failure = NULL; }
            else truth = closed_truth(closed, name, verdict);
            scratch_drop(mark);
            if (truth == (by_cell ? param_cell[c].truth : 1)) continue;
            if (truth < 0) {
                snprintf(reason, sizeof reason, "non riesco a rileggere le soluzioni scritte: %s", verdict->reason);
                verdict->reason = reason;
            } else {
                unjustified_steps++;
                verdict->reason = "le soluzioni scritte, rilette, non coincidono con la condizione in un valore del parametro";
            }
            verdict->outcome = NOT_PROVED;
            return 0;
        }
    return 1;
}

/* 18t-g. Ritorna la verità della condizione f quando il parametro di nome
 * name vale il razionale at, per quanto la si può stabilire con il solo
 * conto diretto sui numeri: 1 vera, 0 falsa, -1 non si sa.
 *
 * Un confronto nel solo parametro si calcola (sign_holds_at()). Di un
 * quantificatore interno si provano PARAM_GRID valori della sua variabile:
 * un valore in cui la condizione non vale smentisce un "per ogni", uno in
 * cui vale conferma un "esiste"; il contrario non si può dire, perché i
 * valori provati sono pochi. I connettivi si calcolano dalle parti, con la
 * logica a tre valori (truth_join()), e danno una risposta anche quando una
 * parte non la dà: "falso e qualcosa" è falso. */
static int grid_truth(const Formula *f, int name, Frac at) {
    if (f->kind == F_NOT || f->kind == F_AND || f->kind == F_OR || f->kind == F_IMPLIES || f->kind == F_IFF) {
        int a = grid_truth(f->a, name, at), b = f->kind == F_NOT ? -1 : grid_truth(f->b, name, at);
        return truth_join(f->kind, a, b);
    }
    if (f->kind == F_FORALL || f->kind == F_EXISTS) {
        Frac value[PARAM_GRID];
        Scratch mark = scratch_mark();
        Formula *body = formula_with(f->a, name, node_rational((Wide){at.num, at.den}));
        int every = f->kind == F_FORALL, found = -1;
        numbers_sample(&f->numbers, value, PARAM_GRID);
        for (int i = 0; i < PARAM_GRID && found < 0; i++) {
            failure = NULL;
            int holds = sign_holds_at(body, f->variable, value[i]);
            if (!failure && holds != every) found = !every;
        }
        failure = NULL;
        scratch_drop(mark);
        return found;
    }
    failure = NULL;
    int holds = sign_holds_at(f, name, at);
    if (failure) holds = -1;
    failure = NULL;
    return holds;
}

/* 18t-g. Ritorna 0 se in uno dei valori della griglia del parametro di nome
 * name, che varia in set, le celle sono smentite: se la condizione f, con
 * quel valore al posto del parametro, risulta falsa dove dovrebbe essere
 * vera, o il contrario. Dovrebbe essere vera nelle celle con truth a 1
 * (by_cell = 1), oppure dappertutto (by_cell = 0). La si guarda nei due modi
 * di 18t-g: con la tabella dei segni (closed_truth()) e con il conto diretto
 * (grid_truth()). Dove un modo non sa rispondere, lì non dice nulla. */
static int grid_agrees(const Formula *f, int name, const NumberSet *set, int by_cell) {
    Frac simple[PARAM_GRID];
    numbers_sample(set, simple, PARAM_GRID);
    for (int i = 0; i < 2 * PARAM_REACH + 1 + PARAM_GRID; i++) {
        /* Prima i quarti, poi i razionali più semplici: qualcuno si ripete,
         * e non fa danno. */
        Wide at = i <= 2 * PARAM_REACH ? wide_make(i - PARAM_REACH, 4) : (Wide){simple[i - 2 * PARAM_REACH - 1].num, simple[i - 2 * PARAM_REACH - 1].den};
        Verdict unused = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
        Scratch mark = scratch_mark();
        Formula *closed = formula_with(f, name, node_rational(at));
        int decided = failure ? -1 : closed_truth(closed, name, &unused);
        int seen = grid_truth(f, name, (Frac){(long long)at.num, (long long)at.den});
        scratch_drop(mark);
        failure = NULL;
        int cell = param_cell_of(at), expected = by_cell ? param_cell[cell].truth : 1;
        if (failure) { failure = NULL; continue; }
        if ((decided >= 0 && decided != expected) || (seen >= 0 && seen != expected)) return 0;
    }
    return 1;
}

/* 18t-h1. Legge i coefficienti f[0..MAX_PARAM_DEGREE] di un polinomio in x,
 * che devono essere polinomi nel solo parametro (atomo a) a coefficienti
 * razionali, e mette in out[j] il coefficiente di x^j moltiplicato per L, lo
 * stesso intero positivo per tutti: il minimo comune multiplo dei
 * denominatori. Mette in *degree il grado in x, il più grande j con f[j] non
 * nullo (-1 se sono tutti nulli). Ritorna 0 se un coefficiente ha un'altra
 * forma (un'altra lettera, un esponente negativo, frazionario o oltre
 * MAX_UNI, un numero complesso); se L esce da COEF_LIMIT annota un errore.
 *
 * Perché lo stesso L per tutti: in un determinante di 18t-h2 ogni riga è
 * fatta di coefficienti di f, quindi resta moltiplicata per L, e il
 * determinante per una potenza di L, che è un fattore costante e non cambia
 * le radici. È un conto a parte da uni_from_poly(), che di ogni polinomio
 * prende il suo multiplo. */
static int projection_integers(const Poly *f, int a, Uni *out, int *degree) {
    __int128 scale = 1;
    for (int j = 0; j <= MAX_PARAM_DEGREE; j++)
        for (int t = 0; t < f[j].count; t++) {
            const Term *term = &f[j].term[t];
            Frac e = term->mono.count ? term->mono.factor[0].exp : frac_int(0);
            if (term->mono.count > 1 || (term->mono.count == 1 && term->mono.factor[0].atom != a) || e.den != 1 || e.num < 0 || e.num > MAX_UNI ||
                term->coef.im.num != 0) return 0;
            scale = scale / gcd128(scale, term->coef.re.den) * term->coef.re.den;
            if (scale > COEF_LIMIT) { fail(SIGN_LIMIT); return 0; }
        }
    *degree = -1;
    for (int j = 0; j <= MAX_PARAM_DEGREE; j++) {
        memset(&out[j], 0, sizeof out[j]);
        out[j].degree = -1;
        for (int t = 0; t < f[j].count; t++) {
            const Term *term = &f[j].term[t];
            int e = term->mono.count ? (int)term->mono.factor[0].exp.num : 0;
            out[j].c[e] = (__int128)term->coef.re.num * (scale / term->coef.re.den);
            if (e > out[j].degree) out[j].degree = e;
        }
        if (out[j].degree >= 0) *degree = j;
    }
    return 1;
}

/* 18t-h2. Ritorna q^d p(n / q) = c_0 q^d + c_1 n q^(d-1) + ... + c_d n^d, con
 * at = n / q, il numero p(at) moltiplicato per q^d: un intero, senza
 * frazioni. d non è meno del grado di p. Annota un errore se un conto esce
 * dai 128 bit.
 *
 * Due polinomi di grado al più d calcolati così nello stesso punto hanno lo
 * stesso rapporto dei loro valori veri: il fattore q^d è lo stesso. */
static __int128 uni_homogeneous(const Uni *p, int d, Frac at) {
    __int128 sum = 0, power = 1, term;
    for (int i = d; i >= 0; i--) {
        /* sum: c_d n^(d-i) + ... + c_(i+1) n q^(d-i-1); power: q^(d-i). */
        if (__builtin_mul_overflow(sum, (__int128)at.num, &sum) || __builtin_mul_overflow(i <= p->degree ? p->c[i] : 0, power, &term) ||
            __builtin_add_overflow(sum, term, &sum) || (i > 0 && __builtin_mul_overflow(power, (__int128)at.den, &power))) {
            fail(SIGN_LIMIT);
            return 0;
        }
    }
    return sum;
}

/* 18t-h2. Ritorna il determinante della matrice di interi m, di size righe e
 * colonne, che il conto rovina. Annota un errore se un conto esce dai 128
 * bit.
 *
 * Eliminazione di Bareiss (E. H. Bareiss, Sylvester's identity and
 * multistep integer-preserving Gaussian elimination, Math. Comp. 22, 1968).
 * È l'eliminazione di Gauss senza frazioni: al passo k ogni elemento sotto
 * e a destra del perno diventa
 *
 *     m[i][j] = (m[k][k] m[i][j] - m[i][k] m[k][j]) / p,
 *
 * dove p è il perno del passo prima (1 al primo). La divisione è esatta,
 * perché dopo il passo k l'elemento m[i][j] è il determinante della
 * sottomatrice di partenza fatta dalle righe 0..k, i e dalle colonne 0..k, j
 * (identità di Sylvester): un intero. Dopo l'ultimo passo m[size-1][size-1]
 * è il determinante. Un perno nullo si scambia con una riga sotto, che
 * cambia il segno; se sono nulli tutti, la colonna sotto la diagonale è
 * nulla e il determinante è zero. È un altro algoritmo dallo sviluppo di
 * Laplace di minor_determinant(), e lavora sui numeri, non sui polinomi. */
static __int128 bareiss(__int128 m[MAX_MINOR][MAX_MINOR], int size) {
    __int128 previous = 1;
    int sign = 1;
    for (int k = 0; k + 1 < size; k++) {
        if (m[k][k] == 0) {
            int r = k + 1;
            while (r < size && m[r][k] == 0) r++;
            if (r == size) return 0;
            for (int j = 0; j < size; j++) {
                __int128 swap = m[k][j];
                m[k][j] = m[r][j];
                m[r][j] = swap;
            }
            sign = -sign;
        }
        for (int i = k + 1; i < size; i++)
            for (int j = k + 1; j < size; j++) {
                __int128 x, y;
                if (__builtin_mul_overflow(m[k][k], m[i][j], &x) || __builtin_mul_overflow(m[i][k], m[k][j], &y) || __builtin_sub_overflow(x, y, &x)) {
                    fail(SIGN_LIMIT);
                    return 0;
                }
                m[i][j] = x / previous;
            }
        previous = m[k][k];
    }
    return sign * m[size - 1][size - 1];
}

/* 18t-h3. Ritorna 1 se ogni radice reale di p, polinomio nel parametro che
 * non è il polinomio nullo, è uno dei valori critici param_point[]; 0 se
 * no. Annota un errore se i numeri sono troppo grandi.
 *
 * Il conto. Sia s la parte senza quadrati di p, p / mcd(p, p'): ha le stesse
 * radici, ognuna una volta. Il teorema di Sturm conta le sue radici reali
 * distinte, N, tra -B e B, dove B le supera tutte (uni_bound()). Poi si
 * contano i valori critici che sono radici di s, C: uno razionale lo è se s
 * lì vale zero; uno irrazionale è la sola radice del suo polinomio E tra due
 * razionali, e lo è se mcd(E, s), che ha per radici le radici comuni, ne ha
 * una tra quei due, cioè proprio lui. I valori critici sono numeri diversi
 * (18t-h4), quindi C <= N, e C = N vuol dire che ogni radice reale di s è un
 * valore critico. */
static int roots_are_critical(const Uni *p) {
    if (p->degree <= 0) return 1;
    Uni derivative = uni_derivative(p), common = uni_gcd(*p, derivative), s;
    if (failure || !uni_divide(p, &common, &s)) { fail(SIGN_LIMIT); return 0; }
    Wide bound = uni_bound(&s), minus = {-bound.num, 1};
    sturm_build(&s);
    int roots = sturm_changes(minus) - sturm_changes(bound), found = 0;
    for (int k = 0; k < param_points && !failure; k++) {
        const ParamPoint *point = &param_point[k];
        if (point->at.exact) {
            found += uni_sign_at(&s, point->at.low) == 0;
            continue;
        }
        common = uni_gcd(point->element, s);
        if (common.degree < 1) continue;
        sturm_build(&common);
        found += sturm_changes(point->at.low) - sturm_changes(point->at.high) > 0;
    }
    return found == roots;
}

/* 18t-h2, 18t-h3. Ricontrolla il polinomio della proiezione con provenienza
 * kind, first, second e k (come in ProjectionItem), dai coefficienti in x
 * già interi f[0..m] e g[0..n] (g è NULL per a1, che è f[m]): cerca tra
 * param_item[] quello che param_project() ha registrato per lui, e lo
 * confronta con i valori calcolati qui. Ritorna 2 se i due coincidono e sono
 * il polinomio nullo; 1 se coincidono, non lo sono, e ogni radice reale è
 * un valore critico; 0 se qualcosa non torna. Annota un errore se i numeri
 * sono troppo grandi.
 *
 * Perché D + 1 valori bastano. Un polinomio di grado al più D che non è il
 * polinomio nullo ha al più D radici: se si annulla in D + 1 numeri diversi
 * è il polinomio nullo. Quindi due polinomi di grado al più D sono uno c
 * volte l'altro se lo sono in D + 1 numeri: la differenza si annulla in
 * tutti. Qui D limita il grado di psc_k: ogni termine del determinante
 * prende un elemento da ogni riga, n - k righe di coefficienti di f, di grado
 * al più dF nel parametro, e m - k di g, di grado al più dG, quindi
 * D = (n - k) dF + (m - k) dG.
 *
 * Perché il determinante si calcola sui numeri. Calcolare un polinomio nel
 * parametro in un numero a0 rispetta somme e prodotti, e il determinante è
 * fatto di somme e prodotti degli elementi: il valore in a0 del determinante
 * è il determinante della matrice dei valori in a0. La matrice resta quella
 * dei gradi formali m e n anche dove a0 annulla un coefficiente direttivo:
 * psc_k è definito così, e così lo calcola subresultant_lead(). I valori si
 * prendono nei razionali più semplici, 0, 1, -1, 2, -2, 1/2, ...
 * (numbers_sample()), che tengono piccoli i numeri, e moltiplicati per
 * q^d (uni_homogeneous()); il determinante risulta moltiplicato per q^D, e
 * così il polinomio registrato, calcolato con lo stesso D. */
static int projection_item(int kind, int first, int second, int k, const Uni *f, int m, const Uni *g, int n) {
    const ProjectionItem *item = NULL;
    for (int i = 0; i < param_items && !item; i++)
        if (param_item[i].kind == kind && param_item[i].first == first && param_item[i].second == second && param_item[i].k == k) item = &param_item[i];
    if (!item) return 0;

    /* I gradi nel parametro, e D. */
    int df = 0, dg = 0, size = g ? m + n - 2 * k : 1;
    for (int j = 0; j <= m; j++) df = f[j].degree > df ? f[j].degree : df;
    for (int j = 0; g && j <= n; j++) dg = g[j].degree > dg ? g[j].degree : dg;
    int d = g ? (n - k) * df + (m - k) * dg : f[m].degree;
    if (d + 1 > PROJECTION_POINTS || size > MAX_MINOR) { fail(SIGN_LIMIT); return 0; }
    if (item->value.degree > d) return 0;

    /* 18t-h2. I valori nei D + 1 razionali: il coefficiente direttivo, o il
     * determinante. Le prime n - k righe sono x^(n-k-1) f, ..., f, le altre
     * x^(m-k-1) g, ..., g, scritte dalla potenza x^(m+n-k-1) in giù: nella
     * riga r di f la colonna c ha il coefficiente di x^(m-c+r), nella riga
     * r' = r - (n - k) di g quello di x^(n-c+r'). Delle m + n - k colonne si
     * tengono le prime m + n - 2k. */
    NumberSet reals;
    Frac point[PROJECTION_POINTS];
    __int128 value[PROJECTION_POINTS], matrix[MAX_MINOR][MAX_MINOR];
    memset(&reals, 0, sizeof reals);
    reals.reals = 1;
    numbers_sample(&reals, point, d + 1);
    for (int t = 0; t <= d && !failure; t++) {
        if (!g) { value[t] = uni_homogeneous(&f[m], d, point[t]); continue; }
        for (int r = 0; r < size; r++)
            for (int c = 0; c < size; c++) {
                int upper = r < n - k, power = upper ? m - c + r : n - c + r - (n - k);
                matrix[r][c] = power < 0 || power > (upper ? m : n) ? 0 : uni_homogeneous(upper ? &f[power] : &g[power], upper ? df : dg, point[t]);
            }
        value[t] = bareiss(matrix, size);
    }
    if (failure) return 0;

    /* Il confronto: il registrato è c volte il polinomio vero se in ogni
     * punto il rapporto dei due valori è c, quello del primo punto in cui il
     * valore vero non è zero. Il rapporto si confronta ridotto ai minimi
     * termini, senza moltiplicare: così non esce dai 128 bit. E c deve essere
     * positivo: tutti e due i conti moltiplicano psc_k solo per numeri
     * positivi (i denominatori tolti, q^D, j nella derivata), con le righe
     * nello stesso ordine. Se il valore vero è zero dappertutto, il polinomio
     * vero è il polinomio nullo, e tale deve essere il registrato. */
    int t0 = 0;
    while (t0 <= d && value[t0] == 0) t0++;
    if (t0 > d) return item->value.degree < 0 ? 2 : 0;
    if (item->value.degree < 0) return 0;
    Wide ratio = wide_make(uni_homogeneous(&item->value, d, point[t0]), value[t0]);
    if (ratio.num <= 0) return 0;
    for (int t = 0; t <= d && !failure; t++) {
        __int128 recorded = uni_homogeneous(&item->value, d, point[t]);
        if (value[t] == 0) {
            if (recorded != 0) return 0;
            continue;
        }
        Wide here = wide_make(recorded, value[t]);
        if (here.num != ratio.num || here.den != ratio.den) return 0;
    }
    if (failure) return 0;

    /* 18t-h3. Il contenimento. */
    return roots_are_critical(&item->value);
}

/* 18t-h2, 18t-h3. Ricontrolla i psc_k(f, g) con provenienza kind, first e
 * second per k = 0, 1, ..., fino al primo che non è il polinomio nullo: sono
 * quelli che 18t-a chiede. Ritorna 1 se tornano tutti, 0 se no. */
static int projection_first(int kind, int first, int second, const Uni *f, int m, const Uni *g, int n) {
    for (int k = 0; k < (m < n ? m : n); k++) {
        int found = projection_item(kind, first, second, k, f, m, g, n);
        if (found != 2) return found;
    }
    return 1;
}

/* 18t-h4. Ritorna 1 se i valori critici e le celle sono ciò che le decisioni
 * presumono; 0 se no. Annota un errore se i numeri sono troppo grandi.
 *
 *   - I valori critici sono in ordine e i loro intervalli non si toccano:
 *     sono numeri diversi, come vuole 18t-h3.
 *   - Uno irrazionale è la sola radice del suo polinomio E, di secondo grado,
 *     tra i due estremi del suo intervallo, che non sono radici (teorema di
 *     Sturm): così è un numero ben definito. Ed è la più piccola delle due
 *     radici di E esattamente se l'altra sta sopra l'intervallo: è ciò che
 *     dice smaller, con cui quadratic_node() sceglie il segno davanti alla
 *     radice quadrata nel valore della cella.
 *   - Il razionale di una cella che è un intervallo sta tra i due valori
 *     critici che la chiudono; quello di un punto razionale è il punto. */
static int cells_are_sound(void) {
    for (int k = 0; k < param_points && !failure; k++) {
        const ParamPoint *p = &param_point[k];
        if (k + 1 < param_points && wide_cmp(p->at.high, param_point[k + 1].at.low) >= 0) return 0;
        if (p->at.exact) continue;
        Uni e = p->element;
        if (e.degree != 2 || uni_sign_at(&e, p->at.low) == 0 || uni_sign_at(&e, p->at.high) == 0) return 0;
        Wide bound = uni_bound(&e);
        sturm_build(&e);
        if (sturm_changes(p->at.low) - sturm_changes(p->at.high) != 1) return 0;
        if (p->smaller != (sturm_changes(p->at.high) - sturm_changes(bound) == 1)) return 0;
    }
    for (int c = 0; c < param_cells && !failure; c++) {
        Wide sample = param_cell[c].sample;
        if (c % 2) {
            if (param_point[c / 2].at.exact && wide_cmp(sample, param_point[c / 2].at.low) != 0) return 0;
            continue;
        }
        if (c >= 2 && wide_cmp(sample, param_point[c / 2 - 1].at.high) <= 0) return 0;
        if (c / 2 < param_points && wide_cmp(sample, param_point[c / 2].at.low) >= 0) return 0;
    }
    return 1;
}

/* 18t-h. Ricontrolla la proiezione registrata in param_item[] e le celle
 * costruite da lei, con il parametro di atomo a. Va chiamata dopo
 * param_cells_build(), anche dopo le decisioni sulle celle: usa solo
 * param_poly[], param_part[], param_var[], param_item[], param_point[] e
 * param_cell[], che le decisioni non toccano. Ritorna 1 se tutto torna; 0
 * se qualcosa non torna, che è un errore del motore; -1 se un conto esce dai
 * numeri che il controllo sa trattare, e anche se un errore era già
 * annotato prima: allora non conferma nulla. */
static int projection_sound(int a) {
    static Uni part[MAX_PARAM_POLYS][MAX_PARAM_DEGREE + 1];
    int degree[MAX_PARAM_POLYS], sound = 1;

    /* 18t-h1. Ogni polinomio: le sue parti in x, rimoltiplicate per le
     * potenze di x, lo ricompongono, e i coefficienti interi e il grado in x
     * che ne legge projection_integers() sono il punto di partenza di ciò
     * che segue. Non si usa param_degree[]. */
    for (int i = 0; i < param_polys && sound && !failure; i++) {
        size_t before = arena_used;
        Poly sum = {0, NULL};
        for (int j = 0; j <= MAX_PARAM_DEGREE; j++) {
            Poly power = poly_const(num_int(1));
            if (j > 0) power = poly_term((Term){num_int(1), mono_atom(param_var[i], frac_int(j))});
            sum = poly_add(sum, poly_mul(param_part[i][j], power), 0);
        }
        sound = !failure && poly_equal(sum, param_poly[i]) && projection_integers(param_part[i], a, part[i], &degree[i]) && degree[i] >= 0;
        arena_used = before;
    }

    /* 18t-h4, poi 18t-h2 e 18t-h3: gli elementi che la proiezione deve
     * contenere si ricavano qui da part[]. Per ogni polinomio il coefficiente
     * direttivo e i psc_k con la derivata, che si calcola qui; per ogni
     * coppia nella stessa variabile i psc_k. */
    sound = sound && cells_are_sound();
    for (int i = 0; i < param_polys && sound && !failure; i++) {
        Uni derivative[MAX_PARAM_DEGREE + 1];
        int m = degree[i];
        sound = projection_item(1, i, -1, 0, part[i], m, NULL, 0) != 0;
        for (int j = 1; j <= m; j++) derivative[j - 1] = uni_scaled(&part[i][j], j);
        sound = sound && projection_first(2, i, -1, part[i], m, derivative, m - 1);
        for (int j = i + 1; j < param_polys && sound; j++)
            if (param_var[j] == param_var[i]) sound = projection_first(3, i, j, part[i], m, part[j], degree[j]);
    }
    if (failure) {
        failure = NULL;
        return -1;
    }
    return sound;
}

/* 18t-h. Ritorna 1 se projection_sound() conferma la proiezione del
 * parametro di atomo a; altrimenti mette in *verdict l'esito NOT_PROVED con
 * il motivo e ritorna 0. Una discordanza è un errore del motore, e conta in
 * unjustified_steps; un conto troppo grande no. */
static int projection_confirmed(int a, Verdict *verdict) {
    int sound = projection_sound(a);
    if (sound > 0) return 1;
    verdict->outcome = NOT_PROVED;
    if (sound < 0) {
        verdict->reason = "non riesco a ricontrollare la proiezione che dà i valori critici del parametro: i conti escono dai limiti del calcolo esatto";
        return 0;
    }
    unjustified_steps++;
    verdict->reason = "la verifica indipendente della proiezione non conferma i valori critici del parametro";
    return 0;
}

/* Ritorna 1 se in f compare un quantificatore sui numeri reali, o una
 * richiesta di soluzioni. */
static int formula_has_real_letter(const Formula *f) {
    if (!f) return 0;
    if (f->kind == F_SOLVE || ((f->kind == F_FORALL || f->kind == F_EXISTS) && f->numbers.reals)) return 1;
    return formula_has_real_letter(f->a) || formula_has_real_letter(f->b);
}

/* Ritorna 1 se l'enunciato thesis è di quelli di questa regola: eventuali
 * negazioni, poi un quantificatore su un numero reale, o una richiesta di
 * soluzioni nei reali, con un'altra lettera reale all'interno. Gli altri
 * enunciati con relazioni d'ordine restano a decide_by_signs().
 *
 * Una richiesta di soluzioni sotto un quantificatore arriva qui qualunque
 * sia l'insieme del quantificatore: decide_by_signs() non conosce quella
 * forma, e leggerebbe la richiesta come una condizione sempre falsa. Qui
 * riceve la risposta giusta: se l'insieme non è \mathbb{R}, che non è
 * trattata. */
int has_parameter(const Formula *thesis) {
    while (thesis->kind == F_NOT) thesis = thesis->a;
    if (thesis->kind == F_FORALL && thesis->a->kind == F_SOLVE) return 1;
    return (thesis->kind == F_FORALL || thesis->kind == F_EXISTS || thesis->kind == F_SOLVE) && thesis->numbers.reals && formula_has_real_letter(thesis->a);
}

/* Il lavoro di decide_with_parameter(), che ne descrive il contratto. */
static void param_decide(const Formula *thesis, Verdict *verdict) {
    static char text[PARAM_TEXT], where[320];
    int negated;
    const Formula *q = without_negations(thesis, &negated);

    /* Le tre forme: una richiesta di soluzioni sotto il "per ogni" del
     * parametro (request), i valori del parametro (solving), una verifica. */
    const Formula *request = q->kind == F_FORALL && q->a->kind == F_SOLVE ? q->a : NULL;
    int solving = q->kind == F_SOLVE, every = q->kind == F_FORALL, name = q->variable, a = atom_var(name);
    if (!numbers_all_reals(&q->numbers)) { verdict->reason = PARAM_FORM; return; }

    /* 18t-a, 18t-b. La tabella nella lettera del parametro: prima le sue
     * colonne, poi i suoi punti, che sono i valori critici. Lo stato che
     * sign_prepare() si aspetta è quello di una tabella nuova (sign_reset()),
     * senza funzioni goniometriche né esponenziali. */
    sign_reset(name);
    sign_x = a;
    param_polys = param_candidates = param_items = 0;
    failure = NULL;
    param_collect(q->a, name, 0);
    param_project(a);
    if (request && !failure) candidates_build(atom_var(request->variable), a);
    if (!failure) param_cells_build(name);
    if (failure) { verdict->reason = failure; failure = NULL; return; }

    /* La dimostrazione scritta comincia dai valori critici: vanno detti
     * adesso, perché le colonne non sopravvivono alla prima cella. */
    size_t opening = proof_length;
    proof_add("\\textbf{Cases on $%c$.} Each comparison counts as false where one of its sides has no value. "
              "For a fixed value of $%c$ what is left is a statement in one variable, decided by a sign table. "
              "Read as polynomials in that variable, the expressions of the statement keep the same real roots, in the same order, "
              "as $%c$ moves without crossing a real root of one of these: ", name, name, name);
    int listed = 0;
    for (int i = 0; i < sign_polys; i++) {
        if (sign_poly[i].degree <= 0) continue;
        proof_add("%s$", listed++ ? ", " : "");
        put_uni(&sign_poly[i], name);
        proof_add("$");
    }
    proof_add("%s (the leading coefficients, the discriminants and the resultants of those polynomials, and the comparisons in $%c$ alone). "
              "So one value of $%c$ decides for each of these roots and for each interval between two consecutive ones.\n\\begin{itemize}\n",
              listed ? "" : "none", name, name);

    /* 18t-c. Una cella alla volta. Una verifica si ferma alla prima cella
     * che decide: quella che smentisce un "per ogni" o conferma un
     * "esiste". Ciò che ogni decisione lascia nell'arena e tra gli atomi
     * viene tolto subito. */
    int decided = -1;
    for (int c = 0; c < param_cells && decided < 0; c++) {
        ParamCell *cell = &param_cell[c];
        Scratch mark = scratch_mark();
        Formula *closed = formula_with(request ? request->a : q->a, name, cell->value);
        const char *problem = failure;
        proof_add("\\item ");
        put_cell(c, name);
        if (problem) {
            /* La copia non è riuscita: non c'è un enunciato da decidere. */
        } else if (request) {
            /* 18t-e. La richiesta, con il valore della cella: tolti i
             * confronti tra numeri, o non resta nulla da risolvere, oppure
             * la risolve 18p, e dalla sua tabella si leggono le soluzioni. */
            Verdict inner = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
            Formula solve = *request;
            size_t before = proof_length;
            solve.a = closed_reduce(closed, request->variable, name, verdict);
            if (!solve.a) {
                problem = verdict->reason;
            } else if (solve.a == &closed_constant[0] || solve.a == &closed_constant[1]) {
                cell->kind = solve.a == &closed_constant[1] ? 2 : 0;
            } else {
                decide_by_signs(&solve, &inner);
                proof_cut(before);
                if (inner.outcome != SOLVED) {
                    verdict->outcome = inner.outcome;
                    problem = inner.reason ? inner.reason : PARAM_INNER;
                } else if (!cell_solutions(cell, c % 2, solve.a, name, request->variable)) {
                    problem = failure ? failure : PARAM_WRITE;
                }
            }
            if (!problem && cell->kind == 1) proof_add(": the solutions are $%s$.\n", cell->text);
            else if (!problem) proof_add(": %s $%c$ is a solution.\n", cell->kind ? "every" : "no", request->variable);
        } else {
            cell->truth = closed_truth(closed, name, verdict);
            if (cell->truth < 0) problem = verdict->reason;
            else proof_add(": the condition %s.\n", cell->truth ? "holds" : "fails");
            if (!solving && cell->truth >= 0 && cell->truth != every) {
                /* Il valore che decide, per il verdetto: con l'x che
                 * smentisce, se la condizione è un "per ogni x". */
                char value[96];
                decided = c;
                if (c % 2 && !param_point[c / 2].at.exact) snprintf(value, sizeof value, "%s", param_point[c / 2].text);
                else wide_text(cell->sample, value, sizeof value);
                int inner = (q->a->kind == F_FORALL || q->a->kind == F_EXISTS) && param_inner[0];
                snprintf(where, sizeof where, "%c = %s%s%s", name, value, inner ? ", " : "", inner ? param_inner : "");
            }
        }
        scratch_drop(mark);
        failure = NULL;
        if (!problem) continue;
        proof_cut(opening);
        verdict->reason = problem;
        return;
    }
    proof_add("\\end{itemize}\n");
    verdict->method = "con la tabella dei segni, per casi sul parametro";

    /* 18t-d. Una verifica. "Per ogni" è vero se nessuna cella lo smentisce,
     * "esiste" se una lo conferma; una negazione davanti li rovescia. Quando
     * hanno deciso tutte le celle insieme, e non una sola, prima del
     * verdetto si ricontrolla la proiezione (18t-h) e si guarda la griglia
     * (18t-g). */
    if (!solving && !request) {
        int holds = every ? decided < 0 : decided >= 0;
        if (decided < 0 && !projection_confirmed(a, verdict)) {
            proof_cut(opening);
            return;
        }
        if (decided < 0 && !grid_agrees(q->a, name, &q->numbers, 1)) {
            unjustified_steps++;
            proof_cut(opening);
            verdict->outcome = NOT_PROVED;
            verdict->reason = "la verifica indipendente, su una griglia di numeri, non conferma i casi sul parametro";
            return;
        }
        if (decided >= 0) proof_add("At this value the condition %s.", every ? "fails" : "holds");
        else proof_add("The condition %s in every case, hence for every value of $%c$.", every ? "holds" : "fails", name);
        claim_verdict(verdict, holds, negated, decided >= 0 ? where : NULL);
        return;
    }

    /* 18t-d, 18t-e. Le soluzioni scritte; poi 18t-h, 18t-f e 18t-g, che le
     * ricontrollano. Le soluzioni poggiano su tutte le celle, quindi la
     * proiezione va ricontrollata sempre. Per i valori del parametro si
     * rilegge il testo e lo si confronta con le celle. Per le soluzioni con
     * il parametro si controlla l'enunciato "per ogni x, la condizione vale
     * se e solo se valgono le soluzioni scritte"; se le soluzioni sono "ogni
     * x" o "nessun x", che non sono condizioni da rileggere, l'enunciato è
     * la condizione stessa, o la sua negazione. */
    int plain = request ? param_cases(name, request->variable, text, sizeof text) : param_values(name, text, sizeof text);
    if (failure) { verdict->reason = failure; failure = NULL; proof_cut(opening); return; }
    if (!projection_confirmed(a, verdict)) {
        proof_cut(opening);
        return;
    }
    Formula *written = plain ? condition_reread(text) : NULL, *claim = NULL;
    if (plain && !written) {
        unjustified_steps++;
        proof_cut(opening);
        verdict->outcome = NOT_PROVED;
        verdict->reason = "le soluzioni scritte non si lasciano rileggere";
        return;
    }
    if (request) {
        Formula *body = request->a;
        claim = formula_node(F_FORALL, plain ? formula_node(F_IFF, body, written, "") : param_cell[0].kind ? body : formula_node(F_NOT, body, NULL, ""), NULL, "");
        claim->variable = request->variable;
        claim->numbers = request->numbers;
    }
    if ((claim || written) && !param_reread(claim ? claim : written, name, !claim, verdict)) { proof_cut(opening); return; }
    if (!grid_agrees(claim ? claim : q->a, name, &q->numbers, !claim)) {
        unjustified_steps++;
        proof_cut(opening);
        verdict->outcome = NOT_PROVED;
        verdict->reason = "la verifica indipendente, su una griglia di numeri, non conferma le soluzioni scritte";
        return;
    }
    proof_add("Hence the condition holds exactly for $%s$. $\\Box$", text);
    verdict->outcome = SOLVED;
    verdict->detail = text;
    verdict->proof = proof_text;
}

/* 18t. Decide con i casi sul parametro l'enunciato thesis, che è di quelli
 * riconosciuti da has_parameter(): una verifica, i valori del parametro, o
 * le soluzioni con il parametro. Riempie *verdict, con la dimostrazione
 * scritta e il controesempio o le soluzioni; ciò che la regola non tratta
 * resta NON SUPPORTATO, con il motivo.
 *
 * Mentre lavora, i grafici sono spenti: ogni cella passa da
 * decide_by_signs(), che altrimenti ne costruirebbe uno per volta, e il
 * disegno di una cella non è il disegno dell'enunciato. */
void decide_with_parameter(const Formula *thesis, Verdict *verdict) {
    int wanted = figures_wanted;
    figures_wanted = 0;
    param_decide(thesis, verdict);
    figures_wanted = wanted;
}
