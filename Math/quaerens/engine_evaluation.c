/* MODULO engine_evaluation: le successioni note come dati, la valutazione di
 * un albero in una frazione, i test di annullamento (capitoli 10-12).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_evaluation.h,
 * e il resto è static. */
#include "engine_evaluation.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_quantifiers.h"
#include "engine_sign_tables.h"

/* =============================================================================
 * 10. VOCABOLARIO: LE SUCCESSIONI NOTE, COME DATI
 * ============================================================================
 *
 * Il motore non sa cosa sia un fattoriale o un numero di Fibonacci: lo legge
 * da questa tabella. Una successione si può definire in due modi.
 *
 *   10a. Con una formula nell'indice m, scritta nello stesso LaTeX degli
 *        enunciati. Il fattoriale è un prodotto, il numero armonico una
 *        somma: il motore li tratta come ogni altra somma o prodotto.
 *
 *   10b. Con una ricorrenza lineare a coefficienti costanti di ordine d:
 *        X(m+d) = coef[0] X(m+d-1) + ... + coef[d-1] X(m), con i valori
 *        iniziali X(0), ..., X(d-1). Fibonacci è d = 2, coefficienti 1 e 1.
 *
 * Per aggiungere una successione basta una riga qui (per esempio i numeri di
 * Lucas: {'L', NULL, 2, {1, 1}, {2, 1}, NULL}).
 */

Sequence library[] = {
    {'!', "\\prod_{j=1}^{m} j", 0, {0}, {0}, NULL},
    {'H', "\\sum_{j=1}^{m} \\frac{1}{j}", 0, {0}, {0}, NULL},
    {'F', NULL, 2, {1, 1}, {0, 1}, NULL},
};

/* Quanto dell'arena è occupato dal vocabolario: da non svuotare mai. */
size_t arena_keep;

/* Prepara il motore: analizza le definizioni del vocabolario. Va chiamata una
 * volta prima di ogni altra funzione dei capitoli successivi. */
void engine_init(void) {
    /* Il punto da cui si misura la pila (stack_used()): chi chiama questa
     * funzione è in cima al programma, o quasi. */
    char here;
    stack_origin = (uintptr_t)(void *)&here;
    arena_used = 0;
    for (int i = 0; i < LIBRARY_COUNT; i++)
        if (library[i].definition) library[i].tree = parse_expression(library[i].definition);
    arena_keep = arena_used;
}

/* =============================================================================
 * 11. VALUTAZIONE: DALL'ALBERO ALLA FRAZIONE
 * ============================================================================
 *
 * eval() calcola il valore di un nodo come frazione di polinomi negli atomi.
 * Le variabili possono essere "legate" a un valore: l'indice di una somma
 * durante il calcolo del corpo, e soprattutto n, che l'induzione lega di volta
 * in volta a un numero, a se stessa o a n + 1. Una variabile non legata è un
 * parametro dell'enunciato e diventa un atomo.
 *
 * Il punto delicato è riportare ogni risultato agli stessi atomi "in n",
 * qualunque sia il valore legato a n:
 *
 *   - somme e prodotti: eval_bigop(); quelle con n nel coefficiente
 *     binomiale hanno una forma chiusa, che dà il teorema del binomio:
 *     binomial_sum() (11n);
 *   - successioni per ricorrenza: eval_recurrence();
 *   - potenze con esponente simbolico: power() e symbolic_power();
 *   - radici e logaritmi: fractional_power() e logarithm(), che si appoggiano
 *     alla scomposizione in fattori di factorize();
 *   - seni e coseni: exp_i().
 *
 * Nel conto di un'uguaglianza che vale "dove i due membri sono definiti" la
 * scomposizione usa anche i fatti del dominio (11q): i segni che in tutti
 * quei punti, e solo lì, sono certi.
 */

/* Le variabili legate in questo momento: l'ultima aggiunta nasconde le
 * precedenti con lo stesso nome. */
/* I blocchi mantengono stabili gli indirizzi restituiti da env_lookup(),
 * anche se una valutazione ricorsiva aggiunge altri legami. 64 e soltanto
 * la granularita di allocazione, non un massimo: cresce l'indice di blocchi. */
#define ENV_BLOCK_BINDINGS 64
static Binding **env_block;
static size_t env_block_capacity, env_blocks;
int env_count;

/* La cella del legame index, gia allocata: nessuna ricerca o allocazione. */
Binding *env_at(int index) {
    return &env_block[(size_t)index / ENV_BLOCK_BINDINGS][(size_t)index % ENV_BLOCK_BINDINGS];
}

/* Più di zero mentre si valuta una definizione del vocabolario. */
int library_depth;

/* Il più piccolo n per cui tutte le somme e i prodotti scritti nell'enunciato
 * hanno almeno un termine. È il caso base quando l'enunciato non ne indica
 * uno; eval_bigop() lo alza. */
long long default_base;

/* Un valore sotto il quale n non scende mai nell'enunciato in corso. Serve a
 * stabilire il segno di espressioni come n - 1 (vedi factorize()). */
long long domain_floor;

/* I valori dati ai parametri dell'enunciato quando lo si calcola in un punto
 * preciso: il parametro point_name[i] vale point_value[i]. Durante la
 * dimostrazione l'elenco è vuoto e i parametri restano lettere; lo riempie
 * solo la verifica numerica (13e), che lega questi valori per primi: sono
 * quindi i primi point_count posti di `env` (vedi difference()). */
int point_name[MAX_POINT];
Frac point_value[MAX_POINT];
int point_count;

/* I fatti del dominio (11q, più sotto): mentre domain_on è diverso da zero si
 * sta calcolando un'uguaglianza che vale "dove i due membri sono definiti", e
 * ogni domain_fact[i] è un polinomio negli atomi che in tutti quei punti è
 * >= 0. Li accende e li spegne solo vanishes_where_defined() (12d).
 *
 * Warning: un conto ausiliario fatto durante la valutazione, che non calcola
 * una parte dell'enunciato ma una prova con la lettera ausiliaria (come
 * body_is_positive() e binomial_sum()), deve spegnere domain_on finché dura e
 * poi rimetterlo com'era: i fatti valgono per i valori dell'enunciato, non per
 * quella lettera. */
static Poly domain_fact[MAX_DOMAIN_FACTS];
static int domain_fact_count;
static int domain_on;

/* Lega name a value, senza spostare le celle gia visibili. Un fallimento
 * annota anche work_allocation_failed: eventuali tentativi che ripuliscono
 * failure non possono consegnare un risultato basato su una pila incompleta. */
int env_push(int name, Rat value) {
    size_t block = (size_t)env_count / ENV_BLOCK_BINDINGS;
    if (!work_reserve((void **)&env_block, &env_block_capacity, block + 1, sizeof *env_block)) return 0;
    if (block == env_blocks) {
        env_block[block] = calloc(ENV_BLOCK_BINDINGS, sizeof **env_block);
        if (!env_block[block]) { work_allocation_failed = 1; fail(OUT_OF_MEMORY); return 0; }
        env_blocks++;
    }
    *env_at(env_count++) = (Binding){name, value};
    return 1;
}

/* Scioglie l'ultima variabile legata. */
void env_pop(void) { if (env_count > 0) env_count--; }

/* Ritorna il valore legato a name, o NULL se name è un parametro libero. */
const Rat *env_lookup(int name) {
    for (int i = env_count - 1; i >= 0; i--)
        if (env_at(i)->name == name) return &env_at(i)->value;
    return NULL;
}

/* Ritorna 1 se name è legata a un valore che cambia durante il conto: n, o
 * l'indice di una somma. I parametri a cui la verifica numerica ha dato un
 * valore sono legati anche loro, ma a una costante, e non contano. */
static int env_varies(int name) {
    for (int i = env_count - 1; i >= point_count; i--)
        if (env_at(i)->name == name) return 1;
    return 0;
}

Rat eval(const Node *node);

/* Ritorna 1 se name e nascosto da uno degli indici interni attivi. */
int name_shadowed(const NameScope *scope, int name) {
    for (; scope; scope = scope->outer) if (scope->name == name) return 1;
    return 0;
}

/* Ritorna 1 se nel sotto-albero node compare, libera, una variabile che in
 * questo momento è legata a un valore che cambia (vedi env_varies()). shadow collega gli indici di somme interne
 * gia incontrati: sono legati dalla loro somma, non dall'ambiente. */
static int uses_bound_variable(const Node *node, const NameScope *shadow) {
    if (!node) return 0;
    if (node->kind == N_VAR) return !name_shadowed(shadow, node->name) && env_varies(node->name);
    if (node->kind == N_BIGOP) {
        if (uses_bound_variable(node->a, shadow) || uses_bound_variable(node->b, shadow)) return 1;
        NameScope inner = {node->name, shadow};
        return uses_bound_variable(node->c, &inner);
    }
    return uses_bound_variable(node->a, shadow) || uses_bound_variable(node->b, shadow) ||
           uses_bound_variable(node->c, shadow);
}

/* Valuta il corpo della somma o prodotto node con l'indice legato a index. */
Rat eval_body(const Node *node, Rat index) {
    env_push(node->name, index);
    Rat value = eval(node->c);
    env_pop();
    return value;
}

/* Ritorna 1 se l'atomo è non negativo per ogni n ammesso: n stesso, quando
 * parte da zero o più; la lettera ausiliaria; le potenze di un numero primo;
 * i prodotti di fattori positivi. */
int atom_is_nonnegative(int atom) {
    const Atom *a = &atoms[atom];
    if (a->kind == ATOM_VAR) return a->id == VAR_SLACK || (a->id == induction_var && domain_floor >= 0);
    if (a->kind == ATOM_BIGOP) return a->positive;
    return a->kind == ATOM_POW && a->base == BASE_PRIME;
}

int poly_is_real(Poly p);

/* Ritorna 1 se l'atomo ha certamente valore reale. Le variabili sono numeri
 * reali per convenzione; non lo sono gli atomi e^{i M}, e per prudenza nemmeno
 * somme e prodotti, il cui termine potrebbe contenerne. */
int atom_is_real(int atom) {
    const Atom *a = &atoms[atom];
    if (a->kind == ATOM_BIGOP) return 0;
    if (a->kind != ATOM_POW) return 1;
    if (a->base == BASE_EI) return 0;
    if (a->base == BASE_ATOM) return atom_is_real((int)a->id);
    return a->base == BASE_PRIME || poly_is_real(base_polys[a->id]);
}

/* Ritorna 1 se p ha certamente valore reale: coefficienti reali e atomi
 * reali. */
int poly_is_real(Poly p) {
    for (int i = 0; i < p.count; i++) {
        if (p.term[i].coef.im.num != 0) return 0;
        for (int f = 0; f < p.term[i].mono.count; f++)
            if (!atom_is_real(p.term[i].mono.factor[f].atom)) return 0;
    }
    return 1;
}

/* Ritorna 1 se p è evidentemente positivo: una somma di termini non negativi
 * con coefficiente positivo, uno dei quali è una costante. Un termine è non
 * negativo se ogni suo fattore è un atomo non negativo oppure una potenza pari
 * di un atomo reale, come x^2.
 *
 * È una condizione sufficiente, non necessaria: n^2 - n + 1 è positivo ma non
 * la soddisfa. */
static int poly_is_positive(Poly p) {
    int constant = 0;
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        if (t->coef.im.num != 0 || t->coef.re.num <= 0) return 0;
        for (int f = 0; f < t->mono.count; f++) {
            const Factor *factor = &t->mono.factor[f];
            int even = factor->exp.den == 1 && factor->exp.num % 2 == 0;
            if (!atom_is_nonnegative(factor->atom) && !(even && atom_is_real(factor->atom))) return 0;
        }
        if (t->mono.count == 0) constant = 1;
    }
    return constant;
}

/* Ritorna 1 se il corpo di node è positivo per ogni indice da lower in su.
 *
 * Il corpo viene valutato nell'indice lower + t, dove t è una lettera
 * ausiliaria che vale zero o più: se numeratore e denominatore del risultato
 * sono evidentemente positivi, il corpo lo è per ogni t. Per il fattoriale il
 * corpo è l'indice stesso, e in 1 + t dà 1 + t: positivo.
 *
 * Un errore durante questa prova non riguarda l'enunciato e viene scartato. */
static int body_is_positive(const Node *node, long long lower) {
    const char *saved = failure;
    int recording = conditions_on, domain = domain_on;

    /* È una prova fatta con una lettera ausiliaria, non un conto
     * dell'enunciato: le sue divisioni non pongono condizioni, e i fatti del
     * dominio (11q) non la riguardano. Il risultato resta nell'atomo anche
     * dopo il conto in cui è nato: per questo non deve dipendere da loro. */
    conditions_on = domain_on = 0;
    Rat value = eval_body(node, rat_add(rat_int(lower), rat_atom(atom_var(VAR_SLACK)), 0));
    int positive = failure == saved && poly_is_positive(value.num) && poly_is_positive(value.den);
    failure = saved;
    conditions_on = recording;
    domain_on = domain;
    return positive;
}

/* Lo stato della regola 11n, il teorema del binomio (binomial_sum(), più
 * sotto). binomial_ok dice che la regola si può usare: lo decide chi poi la
 * dichiara nella dimostrazione scritta (induct(), capitolo 13), e
 * binomial_used gli dice se è stata usata. binomial_skip è il coefficiente
 * binomiale che la regola sta trattando come 1 mentre calcola il resto del
 * termine, o NULL; binomial_live dice che in quel conto la lettera
 * ausiliaria sta al posto dell'indice della somma, che è un intero. */
int binomial_ok, binomial_used, binomial_live;
static const Node *binomial_skip;

/* Prototipo in avanti necessario: la regola valuta il termine della somma
 * (eval()) e ne eleva dei pezzi a potenza (power()), e la valutazione di una
 * somma la chiama. */
static int binomial_sum(const Node *node, long long lower, Rat upper, Rat *out);

/* Valuta una somma o un prodotto.
 *
 * Sia lower l'estremo inferiore (un intero) e a n + c il valore dell'estremo
 * superiore con le variabili legate attuali. Tre casi.
 *
 * 11a. a = 0: gli estremi sono numeri. Si svolge: il corpo viene valutato per
 *      ogni indice da lower a c e i risultati sommati (o moltiplicati). Se
 *      c = lower - 1 non ci sono termini e il risultato è 0 (o 1).
 *
 * 11b. a > 0: l'estremo dipende da n. Il risultato è un atomo, che rappresenta
 *      la somma fino a un estremo di riferimento a n + r, corretto con i
 *      termini di differenza:
 *
 *          somma fino ad a n + c  =  atomo + corpo(a n + r + 1) + ... + corpo(a n + c)
 *
 *      se c > r, e con i termini da c + 1 a r sottratti se c < r. Per i
 *      prodotti si moltiplica e si divide. È il cuore dell'induzione: con n+1
 *      al posto di n, la somma fino a n diventa "atomo più ultimo termine".
 *
 *      Il riferimento r è l'estremo con cui l'atomo viene chiesto la prima
 *      volta, cioè quello scritto nell'enunciato (la prima valutazione è con n
 *      legato a se stesso). Scegliere invece sempre r = 0 sarebbe sbagliato:
 *      per una somma da 5 a n + 10 l'atomo "somma da 5 a n" non avrebbe
 *      termini per n piccolo.
 *
 *      Il caso richiede che il corpo dipenda solo dal proprio indice e da
 *      parametri: se dipendesse da n, passando a n+1 cambierebbero tutti i
 *      termini e non basterebbe aggiungere l'ultimo; se dipendesse dall'indice
 *      di una somma esterna, lo stesso atomo indicherebbe somme diverse.
 *
 * 11n. Il termine dipende da n attraverso un coefficiente binomiale: la
 *      somma ha una forma chiusa, che dà il teorema del binomio
 *      (binomial_sum()). */
static Rat eval_bigop(const Node *node) {
    int product = node->op;
    long long lower, a, c;
    Rat upper = eval(node->b);
    if (!rat_integer(eval(node->a), &lower)) { fail("estremo inferiore di somma o prodotto non costante"); return rat_int(0); }
    if (!rat_affine(upper, &a, &c)) { fail("estremo superiore non della forma a n + c"); return rat_int(0); }

    /* 11a. Estremi numerici: si svolge. */
    if (a == 0) {
        if (c < lower - 1) { fail("somma o prodotto con estremo superiore troppo piccolo"); return rat_int(0); }
        if (c - lower >= MAX_UNROLL) { fail("somma o prodotto con troppi termini da svolgere"); return rat_int(0); }
        Rat total = rat_int(product ? 1 : 0);
        for (long long k = lower; k <= c && !failure; k++) {
            Rat value = eval_body(node, rat_int(k));
            total = product ? rat_mul(total, value) : rat_add(total, value, 0);
        }
        return total;
    }

    /* 11b. Estremo che dipende da n: atomo più termini di differenza. */
    if (a < 0) { fail("estremo superiore decrescente in n"); return rat_int(0); }
    NameScope index_scope = {node->name, NULL};
    if (uses_bound_variable(node->a, NULL) || uses_bound_variable(node->c, &index_scope)) {
        /* 11n. */
        Rat closed;
        if (!product && binomial_ok && binomial_sum(node, lower, upper, &closed)) {
            /* Come in 11b: la somma deve avere almeno un termine, e N = a n + c
             * deve essere un naturale. */
            long long need = lower - c;
            need = (need > 0) ? (need + a - 1) / a : -((-need) / a);
            if (library_depth == 0 && need > default_base) default_base = need;
            binomial_used = 1;
            return closed;
        }
        fail("somma o prodotto il cui termine dipende da n: aggiungere l'ultimo termine non basta");
        return rat_int(0);
    }
    int known = atom_count;
    int atom = atom_bigop(node, a, c);
    long long reference = atoms[atom].offset;

    /* Alla nascita di un atomo prodotto si stabilisce se è positivo: lo usano
     * radici e logaritmi (vedi factorize()). */
    if (atom_count > known && product) atoms[atom].positive = body_is_positive(node, lower);
    if (c - reference > MAX_UNROLL || reference - c > MAX_UNROLL) { fail("troppi termini di differenza"); return rat_int(0); }

    /* Solo le somme scritte nell'enunciato decidono il caso base: devono avere
     * almeno un termine, cioè a n + c >= lower. */
    if (library_depth == 0) {
        long long need = lower - c;
        need = (need > 0) ? (need + a - 1) / a : -((-need) / a);
        if (need > default_base) default_base = need;
    }

    Rat total = rat_atom(atom);
    Rat an = rat_mul(rat_int(a), rat_atom(atom_var(induction_var)));
    for (long long j = reference + 1; j <= c && !failure; j++) {
        Rat value = eval_body(node, rat_add(an, rat_int(j), 0));
        total = product ? rat_mul(total, value) : rat_add(total, value, 0);
    }
    for (long long j = c + 1; j <= reference && !failure; j++) {
        Rat value = eval_body(node, rat_add(an, rat_int(j), 0));
        rewriting = product;
        total = product ? rat_div(total, value) : rat_add(total, value, 1);
        rewriting = 0;
    }
    return total;
}

/* Valuta X(index) per la successione s del vocabolario definita per ricorrenza
 * (caso 10b), con index = a n + c.
 *
 * Si tiene una finestra di d valori consecutivi X(t), ..., X(t+d-1) e la si fa
 * scorrere di un posto alla volta:
 *
 *   avanti:   X(t+d) = coef[0] X(t+d-1) + ... + coef[d-1] X(t)
 *   indietro: X(t-1) = (X(t+d-1) - coef[0] X(t+d-2) - ... - coef[d-2] X(t)) / coef[d-1]
 *
 * La seconda è la prima risolta rispetto al termine più vecchio.
 *
 * Se a = 0 la finestra parte dai valori iniziali X(0), ..., X(d-1), che sono
 * numeri, e dopo c passi contiene il numero X(c). Se a > 0 parte dagli atomi
 * X(a n), ..., X(a n + d - 1), e dopo c passi esprime X(a n + c) come loro
 * combinazione: per Fibonacci, F(n+2) = F(n) + F(n+1). */
static Rat eval_recurrence(int sequence, Rat index) {
    const Sequence *s = &library[sequence];
    int d = s->order;
    long long a, c;
    if (!rat_affine(index, &a, &c) || a < 0) { fail("indice di successione non della forma a n + c"); return rat_int(0); }
    if (c > MAX_UNROLL || c < -MAX_UNROLL) { fail("indice di successione troppo lontano"); return rat_int(0); }

    /* Finestra iniziale. */
    Rat window[MAX_ORDER];
    for (int j = 0; j < d; j++)
        window[j] = (a == 0) ? rat_int(s->init[j]) : rat_atom(atom_rec(sequence, a, j));

    /* Passi in avanti. */
    for (long long step = 0; step < c && !failure; step++) {
        Rat next = rat_int(0);
        for (int i = 0; i < d; i++) next = rat_add(next, rat_mul(rat_int(s->coef[i]), window[d - 1 - i]), 0);
        for (int j = 0; j + 1 < d; j++) window[j] = window[j + 1];
        window[d - 1] = next;
    }

    /* Passi all'indietro. */
    for (long long step = 0; step < -c && !failure; step++) {
        Rat previous = window[d - 1];
        for (int i = 0; i + 1 < d; i++)
            previous = rat_add(previous, rat_mul(rat_int(s->coef[i]), window[d - 2 - i]), 1);
        previous = rat_div(previous, rat_int(s->coef[d - 1]));
        for (int j = d - 1; j > 0; j--) window[j] = window[j - 1];
        window[0] = previous;
    }
    return window[0];
}

/* Valuta il termine di indice index della successione chiamata name. */
static Rat eval_sequence(int name, Rat index) {
    for (int i = 0; i < LIBRARY_COUNT; i++) {
        if (library[i].name != name) continue;
        if (!library[i].definition) return eval_recurrence(i, index);

        /* 10a: si valuta la formula con m legato all'indice. */
        env_push('m', index);
        library_depth++;
        Rat value = eval(library[i].tree);
        library_depth--;
        env_pop();
        return value;
    }
    fail("successione con pedice non presente nel vocabolario");
    return rat_int(0);
}

/* Moltiplica il monomio di out per atom^exp; con exp nullo non fa nulla. */
void term_times(Term *out, int atom, Frac exp) {
    if (exp.num == 0) return;
    Mono factor = mono_atom(atom, exp);
    out->mono = mono_mul(&out->mono, &factor);
}

/* Toglie da *value il suo più piccolo fattore primo: mette il primo in *prime
 * e quante volte divide in *times. Ritorna 0, senza fare nulla, quando *value
 * è 1 o meno. Chiamata ripetutamente elenca la scomposizione in fattori primi.
 *
 * Si prova a dividere per 2, 3, 4, ...: il primo divisore trovato è per forza
 * primo, e se nessuno fino alla radice quadrata divide, il numero stesso è
 * primo. *value non deve superare 10^12, o il ciclo sarebbe troppo lungo. */
int pop_prime(long long *value, long long *prime, long long *times) {
    if (*value <= 1) return 0;
    long long p = 2;
    while (p * p <= *value && *value % p != 0) p++;
    if (p * p > *value) p = *value;
    *prime = p;
    *times = 0;
    while (*value % p == 0) { *value /= p; (*times)++; }
    return 1;
}

/* Ritorna il monomio comune a tutti i termini di p, che non deve essere nullo:
 * per ogni atomo il minimo esponente tra i termini, contando zero dove manca.
 * Con esponenti negativi anche x^{-1} può essere comune:
 * x + 1/x = x^{-1} (x^2 + 1). */
Mono poly_common(Poly p) {
    Mono common = p.term[0].mono;
    for (int i = 1; i < p.count; i++) {
        const Mono *other = &p.term[i].mono;
        Mono low;
        low.count = 0;
        int x = 0, y = 0;
        while (x < common.count || y < other->count) {
            Factor f;
            if (y == other->count || (x < common.count && common.factor[x].atom < other->factor[y].atom)) {
                /* Atomo assente nell'altro termine: conta zero, quindi resta
                 * comune solo un esponente negativo. */
                f = common.factor[x++];
                if (f.exp.num > 0) continue;
            } else if (x == common.count || other->factor[y].atom < common.factor[x].atom) {
                f = other->factor[y++];
                if (f.exp.num > 0) continue;
            } else {
                f = common.factor[x++];
                if (frac_cmp(other->factor[y].exp, f.exp) < 0) f.exp = other->factor[y].exp;
                y++;
            }
            low.factor[low.count++] = f;
        }
        common = low;
    }
    return common;
}

/* Ritorna l'atomo che rappresenta (atom)^m, con m un monomio. Se atom è già
 * una potenza b^{m'} il risultato è b^{m' m}, per la regola (b^p)^q = b^{pq}:
 * così (e^{i x})^n ed e^{i n x} sono lo stesso atomo. */
static int atom_raised(int atom, const Mono *m) {
    if (atoms[atom].kind != ATOM_POW) return atom_pow(BASE_ATOM, atom, m);
    Mono merged = mono_mul(&atoms[atom].exponent, m);
    return atom_pow(atoms[atom].base, atoms[atom].id, &merged);
}

/* Ritorna 1 se il monomio vale un numero intero per ogni n ammesso: è un
 * prodotto di potenze, a esponente intero positivo, di n e di atomi come 2^n.
 * Mentre la regola 11n calcola il termine di una somma conta come intero
 * anche la lettera ausiliaria, che lì sta al posto dell'indice. */
int mono_is_integer(const Mono *m) {
    for (int i = 0; i < m->count; i++) {
        const Atom *a = &atoms[m->factor[i].atom];
        Frac e = m->factor[i].exp;
        if (e.den != 1 || e.num < 0) return 0;
        if (a->kind == ATOM_VAR && (a->id == induction_var || (a->id == VAR_SLACK && binomial_live))) continue;
        if (a->kind == ATOM_POW && a->base == BASE_PRIME && domain_floor >= 0 && mono_is_integer(&a->exponent)) continue;
        return 0;
    }
    return 1;
}

/* Ritorna p^{q m}, dove p è un polinomio non nullo, m un monomio non banale
 * (l'esponente simbolico, per esempio n) e q un razionale.
 *
 * Per riconoscere la stessa potenza scritta in modi diversi, p viene scomposto
 * in fattori di cui si eleva ciascuno separatamente, usando (u v)^e = u^e v^e:
 *
 *     p = (segno o unità immaginaria) * (numero razionale positivo)
 *         * (monomio comune a tutti i termini) * (polinomio primitivo)
 *
 *   11c. Il segno: (-1)^{q m} = e^{i pi q m}. L'unità immaginaria i, che
 *        compare con i seni, è e^{i pi/2}, quindi dà e^{i pi q m / 2}.
 *   11d. Il numero: si scompone in fattori primi, ognuno con il suo atomo.
 *        Così 4^n = (2^n)^2 e 6^n = 2^n 3^n.
 *   11e. Il monomio comune: ogni suo atomo viene elevato con atom_raised().
 *   11f. Il polinomio primitivo, cioè ciò che resta: ha coefficienti interi
 *        senza divisori comuni e primo coefficiente positivo, quindi è lo
 *        stesso per tutti i multipli di p. Se non è 1 diventa la base di un
 *        atomo.
 *
 * La regola (u v)^e = u^e v^e vale per e intero ma non in generale: con basi
 * negative ed esponente non intero può fallire. Per questo la scomposizione si
 * fa solo quando l'esponente q m è un intero per ogni n (11b'); altrimenti la
 * base resta un blocco unico e diventa un atomo così com'è. */
/* Prototipi in avanti inevitabili: le potenze che fanno da lettere sono
 * della ricerca del capitolo 18 (18x), che conosce le variabili generiche;
 * qui servono solo a fondere gli esponenti, (x^{n})^{m} = x^{n m}, che per
 * una base positiva e esponenti interi è vero. Fuori dalla ricerca
 * power_letter() ritorna sempre 0. */
int power_letter(int atom);
int power_exponent(const Mono *m);

static Rat symbolic_power(Poly p, const Mono *m, Frac q) {
    Term out;
    out.coef = num_int(1);
    out.mono.count = 0;
    if (p.count == 0) { fail("zero elevato a un esponente simbolico"); return rat_int(0); }

    /* 11b'. Esponente non intero: nessuna scomposizione. Se la base è un solo
     * atomo lo si eleva direttamente, e una potenza di un primo, che è
     * positiva, può ancora fondere gli esponenti: (2^n)^x = 2^{n x}. */
    if (q.den != 1 || !mono_is_integer(m)) {
        const Term *only = &p.term[0];
        int single = p.count == 1 && only->mono.count == 1 && num_equal(only->coef, num_int(1)) &&
                     only->mono.factor[0].exp.num == 1 && only->mono.factor[0].exp.den == 1;
        int atom = single ? only->mono.factor[0].atom : 0;
        if (single && atoms[atom].kind == ATOM_POW && (atoms[atom].base == BASE_PRIME || (q.den == 1 && power_letter(atom) && power_exponent(m))))
            term_times(&out, atom_raised(atom, m), q);
        else if (single) term_times(&out, atom_pow(BASE_ATOM, atom, m), q);
        else term_times(&out, atom_pow(BASE_POLY, base_poly_intern(p), m), q);
        return (Rat){poly_term(out), poly_const(num_int(1))};
    }

    /* Monomio comune, e ciò che resta dopo averlo raccolto. */
    Mono common = poly_common(p);
    Term divisor;
    divisor.coef = num_int(1);
    divisor.mono = mono_pow(&common, frac_int(-1));
    Poly rest = poly_mul(p, poly_term(divisor));
    if (failure || rest.count == 0) return rat_int(0);

    /* Contenuto numerico. Se tutti i coefficienti sono immaginari puri si
     * raccoglie i; se sono misti non si raccoglie nulla. */
    int imaginary = 1, real = 1;
    for (int i = 0; i < rest.count; i++) {
        if (rest.term[i].coef.re.num != 0) imaginary = 0;
        if (rest.term[i].coef.im.num != 0) real = 0;
    }
    Frac content = frac_int(1);
    if (real || imaginary) {
        /* Massimo comun divisore dei numeratori diviso minimo comune multiplo
         * dei denominatori, con il segno del primo coefficiente. */
        __int128 g = 0, l = 1;
        for (int i = 0; i < rest.count; i++) {
            Frac v = imaginary ? rest.term[i].coef.im : rest.term[i].coef.re;
            g = gcd128(g, v.num);
            l = l / gcd128(l, v.den) * v.den;
            if (l >= COEF_LIMIT) { fail("numeri troppo grandi per il calcolo esatto"); return rat_int(0); }
        }
        Frac first = imaginary ? rest.term[0].coef.im : rest.term[0].coef.re;
        content = frac_make(first.num < 0 ? -g : g, l);
        divisor.coef = num_inv(imaginary ? (Num){frac_int(0), content} : num_frac(content));
        divisor.mono.count = 0;
        rest = poly_mul(rest, poly_term(divisor));
    }

    /* 11c. Segno e unità immaginaria. */
    if (content.num < 0 || imaginary) {
        Mono pi = mono_atom(atom_var(VAR_PI), frac_int(1));
        Mono turn = mono_mul(m, &pi);
        int e = atom_pow(BASE_EI, 0, &turn);
        if (content.num < 0) term_times(&out, e, q);
        if (imaginary) term_times(&out, e, frac_div(q, frac_int(2)));
    }

    /* 11d. Fattori primi di numeratore e denominatore del contenuto. */
    for (int side = 0; side < 2; side++) {
        long long value = side ? content.den : (content.num < 0 ? -content.num : content.num);
        long long prime, times;
        if (value > 1000000000000LL) { fail("numero troppo grande da scomporre in fattori primi"); return rat_int(0); }
        while (pop_prime(&value, &prime, &times))
            term_times(&out, atom_pow(BASE_PRIME, prime, m), frac_mul(frac_int(side ? -times : times), q));
    }

    /* 11e. Monomio comune. */
    for (int i = 0; i < common.count; i++)
        term_times(&out, atom_raised(common.factor[i].atom, m), frac_mul(common.factor[i].exp, q));

    /* 11f. Polinomio primitivo. */
    if (!poly_is_one(rest)) term_times(&out, atom_pow(BASE_POLY, base_poly_intern(rest), m), q);

    return (Rat){poly_term(out), poly_const(num_int(1))};
}

/* Un fattore di una scomposizione: base elevata a power. La base è descritta
 * come negli atomi POW: un primo, un atomo, o un polinomio di `base_polys`. */
typedef struct {
    BaseKind kind;
    long long id;
    Frac power;
} Part;

/* La scomposizione di un polinomio p in fattori di cui è noto il segno:
 * p = (prodotto delle part) * rest. Ogni part ha base non negativa per tutti
 * gli n ammessi; rest raccoglie ciò di cui il segno non è noto, compreso il
 * segno stesso di p, e vale 1 quando non resta nulla. */
typedef struct {
    int count;             /* part valide */
    Part part[MAX_PARTS];
    Poly rest;
} Factorization;

/* Aggiunge alla scomposizione il fattore base^power, sommando l'esponente se
 * la base è già presente. */
static void part_add(Factorization *f, BaseKind kind, long long id, Frac power) {
    for (int i = 0; i < f->count; i++)
        if (f->part[i].kind == kind && f->part[i].id == id) {
            f->part[i].power = frac_add(f->part[i].power, power);
            return;
        }
    if (f->count == MAX_PARTS) { fail("troppi fattori in un radicando o nell'argomento di un logaritmo"); return; }
    f->part[f->count++] = (Part){kind, id, power};
}

/* Ritorna il polinomio c[0] + c[1] n + ... + c[degree] n^degree. */
static Poly poly_univariate(const long long *c, int degree) {
    int n = atom_var(induction_var);
    Term *buffer = terms_alloc(degree + 1);
    if (!buffer) return (Poly){0, NULL};
    int used = 0;
    for (int i = 0; i <= degree; i++) {
        if (c[i] == 0) continue;
        Term t;
        t.coef = num_int(c[i]);
        t.mono.count = 0;
        if (i > 0) t.mono = mono_atom(n, frac_int(i));
        buffer[used++] = t;
    }
    return poly_finish(buffer, degree + 1, used);
}

/* Mette in out i divisori positivi di value (positivo) e ne ritorna il numero,
 * oppure 0 se sono più di MAX_DIVISORS. I divisori vanno a coppie d e
 * value/d, quindi basta cercare d fino alla radice quadrata. */
static int divisors(long long value, long long *out) {
    int count = 0;
    for (long long d = 1; d * d <= value; d++) {
        if (value % d != 0) continue;
        if (count + 2 > MAX_DIVISORS) return 0;
        out[count++] = d;
        if (d != value / d) out[count++] = value / d;
    }
    return count;
}

/* Dice se a n + b divide il polinomio di coefficienti c[0..degree], cioè se
 * -b/a ne è una radice: ritorna 1 se lo è, 0 se non lo è, -1 se i numeri
 * escono dall'aritmetica esatta e non si può dire. Si calcola
 * a^degree * p(-b/a), che è l'intero somma dei c[i] (-b)^i a^{degree-i}, con
 * lo schema di Horner partendo dal coefficiente di grado più alto.
 *
 * Il terzo esito va tenuto distinto dal "no": chi conclude che un polinomio
 * non ha radici (capitolo 18) non può contare su una risposta data per
 * mancanza di cifre. */
static int is_root(const long long *c, int degree, long long a, long long b) {
    __int128 value = 0, a_power = 1;
    for (int i = degree; i >= 0; i--) {
        __int128 scaled, term;
        if (__builtin_mul_overflow(value, (__int128)-b, &scaled) ||
            __builtin_mul_overflow((__int128)c[i], a_power, &term) ||
            __builtin_add_overflow(scaled, term, &value))
            return -1;
        if (i > 0 && __builtin_mul_overflow(a_power, (__int128)a, &a_power)) return -1;
    }
    return value == 0;
}

/* Divide sul posto il polinomio c[0..degree] per a n + b. Ritorna 1 se la
 * divisione è esatta a coefficienti interi, lasciando in c[0..degree-1] il
 * quoziente; altrimenti ritorna 0 e c resta com'era.
 *
 * Se c = (a n + b) q, confrontando i coefficienti: c[degree] = a q[degree-1],
 * c[i] = a q[i-1] + b q[i], c[0] = b q[0]. Si ricavano i q dall'alto. */
static int deflate(long long *c, int degree, long long a, long long b) {
    long long q[MAX_UNIVARIATE + 1];
    if (c[degree] % a != 0) return 0;
    q[degree - 1] = c[degree] / a;
    for (int i = degree - 1; i >= 1; i--) {
        long long rest = c[i] - b * q[i];
        if (rest % a != 0) return 0;
        q[i - 1] = rest / a;
    }
    if (c[0] != b * q[0]) return 0;
    for (int i = 0; i < degree; i++) c[i] = q[i];
    c[degree] = 0;
    return 1;
}

/* Trova le radici razionali del polinomio c[0] + c[1] x + ... + c[degree]
 * x^degree, a coefficienti interi con c[degree] diverso da zero. Le mette,
 * distinte, in root[] (che deve avere degree + 1 posti) e ne ritorna il
 * numero; ritorna -1 se non riesce a stabilirle con certezza.
 *
 * Teorema delle radici razionali. Sia u/v una radice, con u e v interi senza
 * divisori comuni e v > 0. Sostituendo e moltiplicando per v^degree:
 *
 *     c[0] v^d + c[1] u v^{d-1} + ... + c[d] u^d = 0.
 *
 * Tutti i termini tranne il primo contengono u, quindi u divide c[0] v^d; non
 * avendo fattori in comune con v, divide c[0]. Allo stesso modo v divide
 * c[d]. Se c[0] non è zero i candidati sono dunque in numero finito, e
 * provandoli tutti si trovano tutte le radici razionali. Se c[0] è zero, lo
 * zero è una radice: si divide per x e si ricomincia. */
int rational_roots(const long long *c, int degree, Frac *root) {
    int count = 0;

    /* Le potenze di x che dividono il polinomio danno la radice zero. */
    while (degree >= 1 && c[0] == 0) {
        if (!count) root[count++] = frac_int(0);
        c++;
        degree--;
    }
    if (degree < 1) return count;

    /* I candidati: -b/a con a divisore di c[degree] e b di c[0], primi tra
     * loro, con i due segni. is_root(c, degree, a, b) prova la radice -b/a. */
    long long lead[MAX_DIVISORS], tail[MAX_DIVISORS];
    int leads = divisors(llabs(c[degree]), lead), tails = divisors(llabs(c[0]), tail);
    if (!leads || !tails) return -1;
    for (int i = 0; i < leads; i++)
        for (int j = 0; j < tails; j++) {
            if (gcd128(lead[i], tail[j]) != 1) continue;
            for (int sign = -1; sign <= 1; sign += 2) {
                int found = is_root(c, degree, lead[i], sign * tail[j]);
                if (found < 0) return -1;
                if (found) root[count++] = frac_make(-sign * tail[j], lead[i]);
            }
        }
    return count;
}

/* Stacca da p i fattori di primo grado a n + b che sono non negativi per ogni
 * n ammesso: li aggiunge a f e ritorna il quoziente. Se p non è un polinomio
 * nella sola n a coefficienti interi lo ritorna com'è.
 *
 * Teorema delle radici razionali: se una frazione ridotta -b/a è radice di un
 * polinomio a coefficienti interi, allora a divide il coefficiente di grado
 * massimo e b divide il termine noto. I candidati sono quindi in numero
 * finito e si provano tutti. Ciò che resta dopo aver tolto i fattori di primo
 * grado (per esempio n^2 + n + 1) non viene scomposto oltre.
 *
 * a n + b è non negativo per n >= domain_floor quando a > 0 e lo è nel punto
 * più basso, n = domain_floor. */
static Poly split_linear_factors(Poly p, Factorization *f) {
    long long c[MAX_UNIVARIATE + 1], scale;

    /* Coefficienti di p, se è della forma richiesta: devono essere già interi,
     * perché il quoziente va restituito senza cambiarlo di un fattore. */
    int degree = poly_coefficients(p, atom_var(induction_var), c, &scale);
    if (degree < 0 || scale != 1) return p;

    /* Finché si trova una radice si stacca il fattore e si ricomincia: così
     * una radice multipla viene tolta più volte. */
    int found = 1, changed = 0;
    while (found && degree >= 1 && c[0] != 0) {
        long long lead[MAX_DIVISORS], tail[MAX_DIVISORS];
        int leads = divisors(llabs(c[degree]), lead), tails = divisors(llabs(c[0]), tail);
        found = 0;
        for (int x = 0; x < leads && !found; x++)
            for (int y = 0; y < tails && !found; y++)
                for (int sign = -1; sign <= 1 && !found; sign += 2) {
                    long long a = lead[x], b = sign * tail[y];
                    if (a * domain_floor + b < 0) continue;
                    if (is_root(c, degree, a, b) != 1 || !deflate(c, degree, a, b)) continue;
                    long long linear[2] = {b, a};
                    part_add(f, BASE_POLY, base_poly_intern(poly_univariate(linear, 1)), frac_int(1));
                    degree--;
                    found = changed = 1;
                }
    }
    return changed ? poly_univariate(c, degree) : p;
}

/* 11q. I FATTI DEL DOMINIO
 *
 * A che cosa servono. Molte uguaglianze tra espressioni in x si affermano
 * "dove i due membri sono definiti": che F' = f (30a), che la derivata di f
 * è g (27a). In ognuno di quei punti ogni radice di indice pari scritta in
 * un membro ha il radicando >= 0, ogni logaritmo scritto senza valore
 * assoluto ha l'argomento > 0, ogni potenza a esponente costante non intero
 * ha la base >= 0 (come u^{1/3}, 11o). Chi dimostra l'uguaglianza a mano li
 * usa: "dove \sqrt{x} è definita x >= 0, e lì \sqrt[3]{x} = (\sqrt[6]{x})^2".
 * Senza di loro il conto esatto non può: per x < 0 la radice cubica reale di
 * x è definita (11o) e la radice sesta no, e due atomi diversi restano
 * diversi.
 *
 * Che cosa sono. Un fatto è un polinomio negli atomi che vale >= 0 in ogni
 * punto in cui i due membri sono definiti. Si annota (domain_note()) nel
 * punto in cui la valutazione incontra l'operazione che lo chiede: il
 * radicando in fractional_power() con la lettura non negativa (odd = 0),
 * l'argomento in logarithm_of_positive(); e, nei casi dei valori assoluti di
 * derivative_identity() (27a), il segno scelto per ogni |u|. Vengono dai due
 * membri e da un'espressione che è definita dove l'uguaglianza si afferma:
 * la funzione di cui un membro è la derivata, la primitiva (vedi 12d). Si
 * usano in quattro modi:
 *
 *   11q-1. Un atomo reale x con il fatto x >= 0 è un fattore di segno noto
 *          per factorize(): la radice cubica di x diventa x^{1/3}, come il
 *          quadrato della radice sesta, invece di prendere due strade (11o
 *          per la prima, la base "x presa come lettera" per la seconda).
 *   11q-2. Un resto di segno non noto che è c w o c w^2, con w un fatto e c
 *          un razionale positivo, diventa un fattore di segno noto: così
 *          \sqrt{w^2} = w, come \sqrt{\cos^2 x} = \cos x dove \cos x >= 0;
 *          \sqrt{u v} = \sqrt{u} \sqrt{v} quando u >= 0 e v >= 0 sono fatti;
 *          la radice di una frazione i cui due termini sono fatti.
 *   11q-3. |u| = u se u >= 0 è un fatto, |u| = -u se lo è -u.
 *   11q-4. Un radicando perde le potenze intere delle radici che contiene:
 *          (\sqrt{u})^2 = u dove \sqrt{u} è definita. Così il radicando di
 *          \sqrt{1 - (\sqrt{1 - 2x})^2} è 2x, e la radice è \sqrt{2} \sqrt{x}.
 *
 * Perché è giusto. Sia D l'insieme dei punti in cui l'uguaglianza si
 * afferma: quelli in cui i due membri sono definiti (e la funzione derivata,
 * o la primitiva, lo è). Un fatto vale in ogni punto di D: è il valore, in
 * quel punto, di un radicando o di un argomento scritto in un'espressione
 * definita in D, calcolato con regole che in D sono identità, comprese
 * quelle che usano i fatti annotati prima (ognuno vero in D, per lo stesso
 * motivo: si ragiona sull'ordine in cui sono stati annotati). Ogni
 * riscrittura che usa un fatto sostituisce un'espressione con un'altra che
 * ha lo stesso valore in ogni punto di D. Quindi se L - R si riduce a zero,
 * L = R in ogni punto di D, che è proprio ciò che si afferma. In un caso dei
 * valori assoluti tutto questo vale nei punti di D in cui valgono i segni di
 * quel caso, e i casi insieme coprono D. Che D non sia vuoto non lo dice il
 * conto: lo dicono i numeri, perché DIMOSTRATO chiede almeno un punto di
 * prova in cui i due membri sono definiti e uguali (27h, 30b).
 *
 * Una riserva, che c'era già prima dei fatti: dove un fattore di segno noto
 * di un radicando si annulla, la scomposizione può chiedere più di quanto
 * l'espressione scritta chieda (\sqrt{x (x - 1)}, con x >= 0, diventa
 * \sqrt{x} \sqrt{x - 1}, che in x = 0 non è definita). Sono punti in cui il
 * fattore è zero, isolati se non lo è su un intervallo, e non interni a D;
 * le derivate e le primitive si affermano sugli intervalli aperti, dove il
 * conto copre ogni punto.
 *
 * Perché solo lì. Un fatto è vero in D e non fuori: x >= 0, che viene da
 * \sqrt{x}, è falso in x = -1, e con lui \sqrt{x^2} = x. Per questo i fatti
 * non devono entrare in nessuna decisione che parli di altri punti: un
 * FALSO (che dice qualcosa di un punto, e lo decidono i numeri, mai il test
 * di annullamento), un "esiste", la tabella dei segni (che dà il segno in
 * ogni punto di un intervallo, anche dove i fatti non valgono), le
 * condizioni di esistenza di 13c (da controllare, non da supporre), un
 * enunciato con \forall x \in \mathbb{R}, che parla anche dei punti in cui
 * un membro non è definito. domain_on lo accende solo vanishes_where_defined()
 * (12d), che chiamano solo i test di annullamento delle uguaglianze "dove i
 * due membri sono definiti", e lo spegne prima di tornare. Ciò che il conto
 * lascia dopo di sé, gli atomi e le loro basi, non dipende dai fatti: un
 * atomo è una quantità con un significato fisso, e i fatti scelgono solo
 * quali atomi scrivere. L'unica eccezione, il segno di un prodotto \prod
 * deciso quando il suo atomo nasce, è calcolata con i fatti spenti
 * (body_is_positive()). Oggi quel conto, come quello di binomial_sum(), nei
 * due test non avviene: lì n è legata a un numero, e le somme e i prodotti
 * si svolgono (11a). Spegnere i fatti costa una riga e tiene vera la
 * garanzia anche se un giorno avverrà.
 *
 * Che cosa manca. Dividere un resto per un fatto (\sqrt{w^2 v} con v non
 * costante resta un atomo); i fatti che non vengono da ciò che il conto
 * calcola, come |u| <= 1 per l'arcoseno o 1 - \cos x >= 0, che chiede
 * \sqrt{\frac{1 + \cos x}{1 - \cos x}} = \frac{|\sin x|}{1 - \cos x}
 * (vedi tests/derivatives/book_derivatives_beyond_about.tex). */

/* Ritorna 1 se r = c w per un razionale c > 0, che mette in *c. */
static int positive_multiple(Poly r, Poly w, Frac *c) {
    if (!poly_proportional(r, w)) return 0;
    Num ratio = num_mul(r.term[0].coef, num_inv(w.term[0].coef));
    *c = ratio.re;
    return ratio.im.num == 0 && ratio.re.num > 0;
}

/* Annota il fatto r >= 0, se è acceso il conto di un'uguaglianza dove i due
 * membri sono definiti. Il fatto è il polinomio num * den, che ha il segno
 * della frazione dove questa è definita. Una costante non dice nulla, e un
 * multiplo positivo di un fatto già annotato non si ripete. Oltre
 * MAX_DOMAIN_FACTS il fatto si perde: ne segue solo un conto meno
 * semplificato. */
static void domain_note(Rat r) {
    Frac c;
    if (!domain_on || failure) return;
    Poly p = poly_mul(r.num, r.den);
    if (p.count == 0 || (p.count == 1 && p.term[0].mono.count == 0)) return;
    for (int i = 0; i < domain_fact_count; i++)
        if (positive_multiple(p, domain_fact[i], &c)) return;
    if (domain_fact_count < MAX_DOMAIN_FACTS) domain_fact[domain_fact_count++] = p;
}

/* Ritorna 1 se un fatto dice che r >= 0 dove i due membri sono definiti,
 * cioè se num * den è un suo multiplo positivo; -1 se lo dice di -r; 0 se i
 * fatti non lo dicono, e sempre a fatti spenti. */
static int domain_sign(Rat r) {
    Frac c;
    if (!domain_on || failure || r.num.count == 0) return 0;
    Poly p = poly_mul(r.num, r.den), minus = poly_add(poly_const(num_int(0)), p, 1);
    for (int i = 0; i < domain_fact_count; i++) {
        if (positive_multiple(p, domain_fact[i], &c)) return 1;
        if (positive_multiple(minus, domain_fact[i], &c)) return -1;
    }
    return 0;
}

/* 11q-1. Ritorna 1 se l'atomo è reale e un fatto dice che è >= 0. */
static int domain_nonnegative(int atom) {
    return domain_on && atom_is_real(atom) && domain_sign(rat_atom(atom)) > 0;
}

/* 11q-2. Se rest, di segno non noto, è c w^k con w un fatto, k = 1 o 2 e c
 * un razionale positivo, aggiunge a f i fattori primi di c e la base w con
 * esponente k, e ritorna il polinomio 1, ciò che resta; altrimenti ritorna
 * rest. La base w è >= 0 per il fatto stesso, quindi è un fattore come gli
 * altri della scomposizione (vedi Factorization).
 *
 * I quadrati si cercano per primi: il radicando di \sqrt{1 - \sin^2 x} è
 * a sua volta un fatto, e riconoscerlo come tale (k = 1) non direbbe nulla
 * di nuovo, mentre come quadrato di \cos x, quando \cos x >= 0 è un fatto,
 * la radice si estrae. */
static Poly domain_split(Poly rest, Factorization *f) {
    for (int k = 2; k >= 1; k--)
        for (int i = 0; domain_on && !failure && i < domain_fact_count; i++) {
            Frac c;
            Poly power = k == 2 ? poly_mul(domain_fact[i], domain_fact[i]) : domain_fact[i];
            if (!positive_multiple(rest, power, &c)) continue;
            if (c.num > 1000000000000LL || c.den > 1000000000000LL) return rest;
            for (int side = 0; side < 2; side++) {
                long long value = side ? c.den : c.num, prime, times;
                while (pop_prime(&value, &prime, &times)) part_add(f, BASE_PRIME, prime, frac_int(side ? -times : times));
            }
            part_add(f, BASE_POLY, base_poly_intern(domain_fact[i]), frac_int(k));
            return poly_const(num_int(1));
        }
    return rest;
}

/* Scompone il polinomio non nullo p in fattori di segno noto (vedi
 * Factorization). Serve a radici e logaritmi, che si distribuiscono sui
 * fattori solo quando questi sono non negativi:
 *
 *     radice(u v) = radice(u) radice(v),    ln(u v) = ln(u) + ln(v).
 *
 * Tre passi, ognuno dei quali stacca fattori dal polinomio:
 *
 *   11k. Il monomio comune ai termini. I suoi atomi non negativi diventano
 *        fattori; gli altri finiscono in rest.
 *   11l. Il contenuto numerico: il massimo comun divisore dei coefficienti,
 *        scomposto in fattori primi. Il segno resta in rest.
 *   11m. I fattori di primo grado in n, con split_linear_factors().
 *
 * Se i coefficienti non sono tutti reali (succede con seni e coseni) si fa
 * solo il passo 11k. Nel conto di un'uguaglianza dove i due membri sono
 * definiti contano anche i fatti del dominio: un atomo >= 0 per un fatto è
 * di segno noto in 11k (11q-1), e il resto viene confrontato con i fatti
 * (11q-2). */
static Factorization factorize(Poly p) {
    Factorization f;
    f.count = 0;

    /* 11k. Monomio comune. */
    Mono common = poly_common(p);
    Term unknown;
    unknown.coef = num_int(1);
    unknown.mono.count = 0;
    for (int i = 0; i < common.count; i++) {
        int atom = common.factor[i].atom;
        if (atom_is_nonnegative(atom) || domain_nonnegative(atom)) part_add(&f, BASE_ATOM, atom, common.factor[i].exp);
        else term_times(&unknown, atom, common.factor[i].exp);
    }
    Term divisor;
    divisor.coef = num_int(1);
    divisor.mono = mono_pow(&common, frac_int(-1));
    Poly rest = poly_mul(p, poly_term(divisor));

    int real = 1;
    for (int i = 0; i < rest.count; i++)
        if (rest.term[i].coef.im.num != 0) real = 0;
    if (real && !failure) {
        /* 11l. Contenuto: massimo comun divisore dei numeratori diviso minimo
         * comune multiplo dei denominatori. */
        __int128 g = 0, l = 1;
        for (int i = 0; i < rest.count; i++) {
            g = gcd128(g, rest.term[i].coef.re.num);
            l = l / gcd128(l, rest.term[i].coef.re.den) * rest.term[i].coef.re.den;
            if (l >= COEF_LIMIT) { fail("numeri troppo grandi per il calcolo esatto"); break; }
        }
        Frac content = failure ? frac_int(1) : frac_make(g, l);
        if (content.num > 1000000000000LL || content.den > 1000000000000LL) fail("numero troppo grande da scomporre in fattori primi");
        for (int side = 0; side < 2 && !failure; side++) {
            long long value = side ? content.den : content.num, prime, times;
            while (pop_prime(&value, &prime, &times)) part_add(&f, BASE_PRIME, prime, frac_int(side ? -times : times));
        }
        divisor.coef = num_inv(num_frac(content));
        divisor.mono.count = 0;
        rest = poly_mul(rest, poly_term(divisor));

        /* 11m. Fattori di primo grado. */
        if (!failure) rest = split_linear_factors(rest, &f);
    }

    /* 11q-2. Il resto, se è un fatto o il quadrato di un fatto. */
    f.rest = domain_split(poly_mul(rest, poly_term(unknown)), &f);
    return f;
}

/* Ritorna base^q con q razionale non intero: una radice, o una sua potenza.
 *
 * Numeratore e denominatore della base vengono scomposti con factorize() e
 * ogni fattore u diventa l'atomo "u preso come lettera" elevato a q volte il
 * suo esponente: radice(12) = 2 radice(3) nasce così, da 12 = 2^2 * 3.
 *
 * Può restare una parte di segno non noto, per esempio n + a con a parametro.
 * Se resta in uno solo tra numeratore e denominatore la si tratta come gli
 * altri fattori: la base è non negativa per ipotesi (altrimenti la radice non
 * sarebbe definita) e tutti gli altri fattori lo sono, quindi lo è anche lei.
 * Se resta in entrambi non si può dire nulla dei due segni presi da soli, e si
 * rinuncia.
 *
 * 11o. Le radici di indice dispari. Con odd diverso da zero q ha il
 * denominatore dispari m, e la radice è quella reale, definita anche per una
 * base negativa: la radice cubica di -8 è -2. È la lettura di \sqrt[3]{u}
 * nei libri; u^{1/3} scritto come potenza resta invece definito solo per
 * u >= 0, come e^{(1/3) ln u}. La radice reale di indice dispari rispetta i
 * prodotti senza condizioni sui segni, (u v)^{1/m} = u^{1/m} v^{1/m} per
 * ogni u e v reali, perché t -> t^m è una funzione crescente da R in R che
 * rispetta i prodotti, e quindi lo fa anche la sua inversa; e (-1)^{1/m} =
 * -1. Così la parte di segno non noto si distribuisce come le altre: ogni
 * atomo del suo monomio comune riceve il suo esponente (la radice cubica di
 * x^5 è x^{5/3}), il segno esce come (-1)^p con q = p/m, e il polinomio che
 * resta diventa un atomo. Nessuna condizione da annotare.
 *
 * Nel conto di un'uguaglianza dove i due membri sono definiti (11q) la base
 * perde prima le potenze intere delle radici che contiene (11q-4), e con la
 * lettura non negativa (odd = 0) diventa un fatto: base >= 0 lì dove la
 * radice è definita. Una radice dispari non dà fatti, perché è definita per
 * ogni base; ma se un fatto dice che la base è >= 0, factorize() la
 * scompone tutta in fattori di segno noto, e la radice dispari prende la
 * strada di quella pari: per una base >= 0 le due letture coincidono.
 *
 * Prototipo in avanti necessario: 11q-4 usa la regola 12a, che sta nel
 * capitolo del test di annullamento. */
static Poly poly_reduce_radicals(Poly p, int keep_value);
Rat fractional_power(Rat base, Frac q, int odd) {
    Term out;
    Mono none;
    out.coef = num_int(1);
    out.mono.count = none.count = 0;

    /* 11q-4. (\sqrt{u})^2 = u dove \sqrt{u} è definita: il conto non cambia
     * valore in nessun punto in cui i due membri lo sono. Un denominatore
     * che diventa zero vuol dire che in quei punti la base non è mai
     * definita: il conto si ferma, senza dire di più (fail() e non
     * fail_undefined(), che direbbe qualcosa di un punto preciso). */
    if (domain_on) {
        base.num = poly_reduce_radicals(base.num, 1);
        base.den = poly_reduce_radicals(base.den, 1);
        if (base.den.count == 0) { fail("una radice con un denominatore che dove i due membri sono definiti vale zero"); return rat_int(0); }
        if (!odd) domain_note(base);
    }

    /* Zero: 0^q = 0 per q positivo. */
    if (base.num.count == 0) {
        if (q.num < 0) fail_undefined("zero elevato a un esponente negativo");
        return rat_int(0);
    }

    /* Con esponente negativo la base sta a denominatore. */
    if (q.num < 0) require(NEVER_ZERO, base.num, "zero elevato a un esponente negativo");

    Factorization side[2] = {factorize(base.num), factorize(base.den)};
    if (failure) return rat_int(0);
    int loose[2] = {!poly_is_one(side[0].rest), !poly_is_one(side[1].rest)};
    if (loose[0] && loose[1] && !odd) { fail("radice di una frazione in cui non si conosce il segno dei due termini"); return rat_int(0); }
    for (int s = 0; s < 2; s++) {
        Frac direction = frac_int(s ? -1 : 1);

        /* Fattori di segno noto. */
        for (int i = 0; i < side[s].count; i++) {
            const Part *part = &side[s].part[i];
            Frac e = frac_mul(frac_mul(part->power, q), direction);
            term_times(&out, part->kind == BASE_ATOM ? (int)part->id : atom_pow(part->kind, part->id, &none), e);
        }

        /* 11o. La parte di segno non noto, con una radice di indice
         * dispari: il monomio comune, il segno, il polinomio che resta. */
        if (loose[s] && odd) {
            Poly rest = side[s].rest;
            Mono common = poly_common(rest);
            for (int i = 0; i < common.count; i++) term_times(&out, common.factor[i].atom, frac_mul(frac_mul(common.factor[i].exp, q), direction));
            rest = poly_mul(rest, poly_term((Term){num_int(1), mono_pow(&common, frac_int(-1))}));
            if (rest.term[0].coef.im.num == 0 && rest.term[0].coef.re.num < 0) {
                rest = poly_add(poly_const(num_int(0)), rest, 1);
                if (q.num % 2) out.coef = num_neg(out.coef);
            }
            if (rest.count == 1 && rest.term[0].mono.count == 0 && !poly_is_one(rest)) { fail("radice di un numero complesso"); return rat_int(0); }
            if (!poly_is_one(rest)) term_times(&out, atom_pow(BASE_POLY, base_poly_intern(rest), &none), frac_mul(q, direction));
            continue;
        }

        /* Parte di segno non noto. Se è una costante è -1 (o un numero
         * complesso): la base è negativa e la radice non è definita. */
        if (!loose[s]) continue;
        if (side[s].rest.count == 1 && side[s].rest.term[0].mono.count == 0) { fail_undefined("radice di un numero negativo"); return rat_int(0); }

        /* Gli altri fattori sono non negativi: la base lo è se lo è questo. */
        require(NEVER_NEGATIVE, side[s].rest, "radice di un numero negativo");
        term_times(&out, atom_pow(BASE_POLY, base_poly_intern(side[s].rest), &none), frac_mul(q, direction));
    }
    return (Rat){poly_term(out), poly_const(num_int(1))};
}

/* Ritorna ln|x| come combinazione di atomi LN.
 *
 * Il logaritmo del valore assoluto trasforma prodotti in somme senza
 * condizioni sui segni: ln|u v| = ln|u| + ln|v| e ln|u^e| = e ln|u| per ogni
 * u e v non nulli. Si scompongono quindi numeratore e denominatore con
 * factorize() e si sommano i logaritmi dei fattori, ognuno con il suo
 * esponente. Dove l'enunciato scrive ln(x) con x positivo, ln|x| è lo stesso
 * numero.
 *
 * Una potenza p^M di un primo dà M ln(p), così ln(2^n) = n ln 2. */
Rat logarithm(Rat x) {
    if (x.num.count == 0) { fail_undefined("logaritmo di zero"); return rat_int(0); }
    require(NEVER_ZERO, x.num, "logaritmo di zero");
    Rat total = rat_int(0);
    for (int s = 0; s < 2 && !failure; s++) {
        Factorization f = factorize(s ? x.den : x.num);

        /* Fattori di segno noto. */
        for (int i = 0; i < f.count && !failure; i++) {
            const Part *part = &f.part[i];
            Term t;
            t.coef = num_frac(part->power);
            t.mono.count = 0;
            if (part->kind == BASE_ATOM && atoms[part->id].kind == ATOM_POW && atoms[part->id].base == BASE_PRIME) {
                t.mono = atoms[part->id].exponent;
                term_times(&t, atom_ln(BASE_PRIME, atoms[part->id].id), frac_int(1));
            } else {
                term_times(&t, atom_ln(part->kind, part->id), frac_int(1));
            }
            total = rat_add(total, (Rat){poly_term(t), poly_const(num_int(1))}, s);
        }

        /* Parte di segno non noto. Una costante qui è -1, e ln|-1| = 0; un
         * polinomio dà un atomo, con il segno scelto in modo che p e -p, che
         * hanno lo stesso valore assoluto, diano lo stesso atomo. */
        Poly rest = f.rest;
        if (rest.count == 1 && rest.term[0].mono.count == 0) {
            if (rest.term[0].coef.im.num != 0) fail("logaritmo di un numero complesso");
            continue;
        }
        if (rest.count > 0 && rest.term[0].coef.im.num == 0 && rest.term[0].coef.re.num < 0)
            rest = poly_add(poly_const(num_int(0)), rest, 1);
        total = rat_add(total, rat_atom(atom_ln(BASE_POLY, base_poly_intern(rest))), s);
    }
    return total;
}

/* Ritorna ln(x) per un argomento scritto senza valore assoluto, che quindi
 * deve essere positivo. In generale è un'ipotesi dell'enunciato; quando x è un
 * numero la si controlla, e un argomento non positivo è un errore. Quando non
 * lo è, la condizione la annota chi chiama, che conosce l'argomento com'è
 * scritto (vedi require_positive()). Nel conto di un'uguaglianza dove i due
 * membri sono definiti, x > 0 è un fatto del dominio (11q). */
Rat logarithm_of_positive(Rat x) {
    Num value;
    if (rat_number(x, &value) && (value.im.num != 0 || value.re.num <= 0)) {
        fail_undefined("logaritmo di un numero non positivo");
        return rat_int(0);
    }

    domain_note(x);
    return logarithm(x);
}

/* Argomenti degli atomi ATAN dell'enunciato in corso, ciascuno una volta:
 * l'atomo di id k vale l'arcotangente di atan_args[k]. */
Rat atan_args[MAX_ATOMS];
int atan_count;

/* Ritorna arctan(x) come combinazione di atomi.
 *
 * L'argomento deve essere reale. Tre regole portano arcotangenti uguali allo
 * stesso atomo:
 *
 *   - arctan(0) = 0;
 *   - l'arcotangente è dispari, arctan(-u) = -arctan(u): si tiene l'argomento
 *     con numeratore e denominatore di primo coefficiente positivo, e il segno
 *     esce fuori;
 *   - arctan(1) = pi/4, perché tan(pi/4) = 1. Tra gli argomenti razionali è
 *     l'unico valore, con 0, che sia un multiplo razionale di pi greco. */
Rat arctangent(Rat x) {
    if (!poly_is_real(x.num) || !poly_is_real(x.den)) { fail("arcotangente di un'espressione che non è certamente reale"); return rat_int(0); }
    if (x.num.count == 0) return rat_int(0);

    /* Segno: lo si porta fuori. */
    int negative = 0;
    if (x.num.term[0].coef.re.num < 0) { x.num = poly_add(poly_const(num_int(0)), x.num, 1); negative = !negative; }
    if (x.den.term[0].coef.re.num < 0) { x.den = poly_add(poly_const(num_int(0)), x.den, 1); negative = !negative; }

    Rat value;
    if (poly_equal(x.num, x.den)) {
        value = rat_div(rat_atom(atom_var(VAR_PI)), rat_int(4));
    } else {
        /* Cerca un atomo con lo stesso argomento: p1/q1 = p2/q2 quando
         * p1 q2 = p2 q1. */
        int index = 0;
        while (index < atan_count &&
               !poly_equal(poly_mul(x.num, atan_args[index].den), poly_mul(atan_args[index].num, x.den)))
            index++;
        if (index == MAX_ATOMS) { fail("troppe arcotangenti distinte nell'enunciato"); return rat_int(0); }
        if (index == atan_count) atan_args[atan_count++] = x;

        Atom atom = {0};
        atom.kind = ATOM_ATAN;
        atom.id = index;
        atom.depends_on_n = poly_depends_on_n(x.num) || poly_depends_on_n(x.den);
        value = rat_atom(atom_intern(&atom));
    }
    return negative ? rat_add(rat_int(0), value, 1) : value;
}

/* Ritorna base^exponent.
 *
 * 11g. Esponente intero costante: moltiplicazioni ripetute.
 *
 * 11h. Altrimenti l'esponente deve essere un polinomio, cioè una somma di
 *      termini q M con q razionale e M monomio; poiché b^{u+v} = b^u b^v, si
 *      eleva un termine alla volta. Il termine costante (M = 1) è una potenza
 *      intera oppure, se q non è intero, una radice: fractional_power(). Gli
 *      altri passano da symbolic_power(), separatamente per numeratore e
 *      denominatore della base. Così 2^{n+1} diventa 2 * 2^n. */
static Rat power(Rat base, Rat exponent) {
    /* 11g. */
    long long e;
    if (rat_integer(exponent, &e)) return rat_pow_int(base, e);

    /* 11h. */
    if (!poly_is_one(exponent.den)) { fail("esponente con un denominatore che non è un monomio"); return rat_int(0); }
    Rat result = rat_int(1);
    for (int i = 0; i < exponent.num.count && !failure; i++) {
        const Term *t = &exponent.num.term[i];
        Frac q = t->coef.re;
        if (t->coef.im.num != 0) { fail("esponente complesso"); break; }
        if (t->mono.count == 0) {
            result = rat_mul(result, q.den == 1 ? rat_pow_int(base, q.num) : fractional_power(base, q, 0));
        } else {
            /* Un esponente simbolico negativo porta la base a denominatore;
             * uno che non è sempre intero vuole una base non negativa. */
            Mono m = t->mono;
            if (q.num < 0) require(NEVER_ZERO, base.num, "zero elevato a un esponente negativo");
            if (conditions_on && (q.den != 1 || !mono_is_integer(&m)))
                require(NEVER_NEGATIVE, poly_mul(base.num, base.den), "potenza a esponente non intero di un numero negativo");

            /* 1 elevato a qualunque esponente è 1: senza questo passo il
             * denominatore 1 di 2^{x} diventava un atomo (1)^{x}, e le
             * dimostrazioni di 18x lo scrivevano. */
            Rat top = poly_is_one(base.num) ? rat_int(1) : symbolic_power(base.num, &m, q);
            Rat bottom = poly_is_one(base.den) ? rat_int(1) : symbolic_power(base.den, &m, q);
            result = rat_mul(result, rat_div(top, bottom));
        }
    }
    return result;
}

/* 11n. IL TEOREMA DEL BINOMIO
 *
 * Una somma come \sum_{k=0}^{n} \binom{n}{k} \cos(kx) non si tratta
 * aggiungendo l'ultimo termine (11b): passando da n a n + 1 cambiano tutti i
 * termini, perché n sta nel coefficiente binomiale. Ha però una forma
 * chiusa. Per ogni naturale N e ogni numero y, anche complesso,
 *
 *     \sum_{k=0}^{N} \binom{N}{k} y^k = (1 + y)^N:
 *
 * è lo sviluppo del prodotto di N fattori (1 + y), in cui y^k si ottiene
 * scegliendo y da k fattori, e i modi di sceglierli sono \binom{N}{k}.
 * Sommando o sottraendo lo stesso sviluppo scritto per -y restano i termini
 * con k pari, o quelli con k dispari:
 *
 *     \sum_k \binom{N}{2k}   y^{2k}   = ((1 + y)^N + (1 - y)^N) / 2,
 *     \sum_k \binom{N}{2k+1} y^{2k+1} = ((1 + y)^N - (1 - y)^N) / 2,
 *
 * e qui k può arrivare fino a N, perché \binom{N}{m} è zero quando m > N.
 *
 * Come si applica. Il termine della somma deve essere il coefficiente
 * binomiale, che ha sopra l'estremo superiore N e sotto k, 2k oppure 2k + 1,
 * moltiplicato per un'espressione g(k). Si calcola g mettendo al posto
 * dell'indice la lettera ausiliaria t: se ogni termine del risultato
 * contiene t solo all'esponente di potenze b^{t M}, allora quel termine è
 * c y^t, con y il prodotto delle potenze b^M, e c e y senza t. Con
 * \cos(kx) = (e^{ikx} + e^{-ikx}) / 2 i termini sono due, con y = e^{ix} e
 * y = e^{-ix}. A ognuno si applica una delle tre formule; per 2k e 2k + 1,
 * dove g(k) = c r^k, serve un y con y^2 = r, che si ottiene dimezzando gli
 * esponenti (i due valori possibili, y e -y, danno lo stesso risultato).
 *
 * Che cosa resta fuori: g(k) con l'indice fuori dagli esponenti (k \binom{n}{k}),
 * due coefficienti binomiali nello stesso termine, un coefficiente con sotto
 * 3k o k + 1, una radice quadrata che non si sa scrivere, una base 1 + y
 * nulla quando N può essere zero. In tutti questi casi la regola non si
 * applica, e la somma resta non trattata.
 *
 * Che la forma chiusa sia quella giusta lo ricontrolla la verifica del
 * capitolo 13: con un numero al posto di n la somma viene svolta termine per
 * termine (11a), senza passare di qui.
 */

/* Ritorna il coefficiente binomiale per cui è moltiplicata l'espressione
 * node: lo si raggiunge scendendo solo per prodotti, segni meno e numeratori
 * di frazioni. NULL se non c'è. */
static const Node *binomial_factor(const Node *node) {
    if (node->kind == N_CALL && node->op == FN_BINOM) return node;
    if (node->kind == N_MUL) {
        const Node *found = binomial_factor(node->a);
        return found ? found : binomial_factor(node->b);
    }
    return node->kind == N_NEG || node->kind == N_DIV ? binomial_factor(node->a) : NULL;
}

/* Prototipo in avanti necessario: la base di un atomo è un polinomio, fatto
 * di atomi. */
static int poly_has_slack(Poly p);

/* Ritorna 1 se nell'atomo compare, a qualunque livello, la lettera
 * ausiliaria. */
static int atom_has_slack(int atom) {
    const Atom *a = &atoms[atom];
    if (a->kind == ATOM_VAR) return a->id == VAR_SLACK;
    if (a->kind == ATOM_ATAN) return poly_has_slack(atan_args[a->id].num) || poly_has_slack(atan_args[a->id].den);
    if (a->kind != ATOM_POW && a->kind != ATOM_LN) return 0;
    for (int i = 0; a->kind == ATOM_POW && i < a->exponent.count; i++)
        if (atom_has_slack(a->exponent.factor[i].atom)) return 1;
    if (a->base == BASE_ATOM) return atom_has_slack((int)a->id);
    return a->base == BASE_POLY && poly_has_slack(base_polys[a->id]);
}

/* Ritorna 1 se in p compare la lettera ausiliaria. */
static int poly_has_slack(Poly p) {
    for (int i = 0; i < p.count; i++)
        for (int f = 0; f < p.term[i].mono.count; f++)
            if (atom_has_slack(p.term[i].mono.factor[f].atom)) return 1;
    return 0;
}

/* Se il fattore `atom` elevato a e di un termine di g(t) è una potenza
 * b^{t M} (vedi 11n), moltiplica *y per ciò che diventa con 1 al posto di t,
 * elevato a e / halves: (b^M)^{e / halves}; halves è 1, oppure 2 quando serve
 * la radice quadrata. Ritorna 1 se ci riesce; 0 se t compare in un altro
 * modo, o se la potenza chiesta non si sa scrivere.
 *
 * Un esponente non intero si accetta solo dove non c'è da scegliere un ramo
 * della radice: sugli atomi e^{i M}, per cui (e^{i M})^q vuol dire e^{i q M},
 * e sui numeri: un primo ha il suo atomo "radice", e di un razionale che è
 * un quadrato, o il suo opposto, la radice è un razionale, per i se serve. */
static int binomial_ratio(int atom, Frac e, int halves, Rat *y) {
    const Atom *a = &atoms[atom];
    int slack = atom_var(VAR_SLACK);
    Frac inside = mono_exponent(&a->exponent, slack), q = frac_div(e, frac_int(halves));
    Mono rest = mono_with_exponent(&a->exponent, slack, frac_int(0)), none = {0};
    Num number;
    if (frac_cmp(inside, frac_int(1)) != 0) return 0;
    for (int i = 0; i < rest.count; i++)
        if (atom_has_slack(rest.factor[i].atom)) return 0;
    if ((a->base == BASE_ATOM && atom_has_slack((int)a->id)) || (a->base == BASE_POLY && poly_has_slack(base_polys[a->id]))) return 0;

    /* b^M: un atomo, oppure, con M = 1, la base stessa. Di un atomo e^{i M}
     * o p^M, e di un primo, si prende qualunque potenza razionale. */
    int letter = -1;
    Rat value;
    if (a->base == BASE_EI || rest.count > 0) letter = atom_pow(a->base, a->id, &rest);
    else if (a->base == BASE_PRIME) letter = atom_pow(BASE_PRIME, a->id, &none);
    if (a->base == BASE_PRIME && rest.count == 0) value = rat_int(a->id);
    else if (letter >= 0) value = rat_atom(letter);
    else if (a->base == BASE_ATOM) value = rat_atom((int)a->id);
    else value = (Rat){base_polys[a->id], poly_const(num_int(1))};
    if (q.den == 1) { *y = rat_mul(*y, rat_pow_int(value, q.num)); return !failure; }
    if (letter >= 0 && (a->base == BASE_EI || a->base == BASE_PRIME)) {
        Term power = {num_int(1), mono_atom(letter, q)};
        *y = rat_mul(*y, (Rat){poly_term(power), poly_const(num_int(1))});
        return !failure;
    }

    /* La radice quadrata di un numero: +-(u/v)^2. */
    if (q.den != 2 || !rat_number(value, &number) || number.im.num != 0 || number.re.num == 0) return 0;
    long long top = number.re.num < 0 ? -number.re.num : number.re.num, bottom = number.re.den, u = 0, v = 0;
    if (top > 1000000000000LL || bottom > 1000000000000LL) return 0;
    while (u * u < top) u++;
    while (v * v < bottom) v++;
    if (u * u != top || v * v != bottom) return 0;
    Rat root = {poly_const(number.re.num < 0 ? (Num){frac_int(0), (Frac){u, v}} : num_frac((Frac){u, v})), poly_const(num_int(1))};
    *y = rat_mul(*y, rat_pow_int(root, q.num));
    return !failure;
}

/* Ritorna base^upper per la regola 11n, dove upper = a n + c è l'estremo
 * superiore di una somma. È power(), tranne che per la base zero, che lì è
 * un errore: 0^N vale 0 quando N è almeno 1, cioè quando lo è per il più
 * piccolo n ammesso; se N può essere zero, dove 0^0 = 1, non c'è un valore
 * solo e resta un errore. Capita con y = -1: la somma a segni alterni dei
 * coefficienti binomiali è (1 - 1)^N. */
static Rat binomial_power(Rat base, Rat upper) {
    long long a, c;
    if (base.num.count == 0 && rat_affine(upper, &a, &c) && a > 0 && a * domain_floor + c >= 1) return rat_int(0);
    return power(base, upper);
}

/* 11n. Se la somma node, da lower a upper, ha per termine un coefficiente
 * binomiale per una somma di termini c y^k, come descritto sopra, mette in
 * *out la sua forma chiusa e ritorna 1. Ritorna 0, senza lasciare errori, se
 * la regola non si applica. upper è il valore dell'estremo superiore, a n + c
 * con a > 0. */
static int binomial_sum(const Node *node, long long lower, Rat upper, Rat *out) {
    const Node *binomial = binomial_factor(node->c);
    const char *saved = failure;
    int slack = atom_var(VAR_SLACK), listed = conditions_on, step = 0, shift = 0, fits = binomial && !failure && lower >= 0 && lower <= MAX_UNROLL;
    int domain = domain_on;
    Rat total = rat_int(0), one = rat_int(1), g = one;

    /* Il termine con t al posto dell'indice: sopra il coefficiente deve
     * esserci l'estremo superiore, sotto step t + shift; g è il resto. I
     * fatti del dominio (11q) valgono per i valori dell'enunciato, non per
     * la lettera t: la regola li spegne finché lavora. */
    domain_on = 0;
    if (fits) {
        env_push(node->name, rat_atom(slack));
        binomial_live = 1;
        Rat top = eval(binomial->a), bottom = eval(binomial->b);
        fits = !failure && rat_add(top, upper, 1).num.count == 0 && poly_is_one(bottom.den);
        for (int i = 0; fits && i < bottom.num.count; i++) {
            const Term *t = &bottom.num.term[i];
            int constant = t->mono.count == 0, linear = t->mono.count == 1 && t->mono.factor[0].atom == slack && frac_cmp(t->mono.factor[0].exp, frac_int(1)) == 0;
            if (t->coef.im.num != 0 || t->coef.re.den != 1 || (!constant && !linear)) fits = 0;
            else if (constant) shift = (int)t->coef.re.num;
            else step = (int)t->coef.re.num;
        }
        fits = fits && ((step == 1 && shift == 0) || (step == 2 && (shift == 0 || shift == 1)));
        if (fits) {
            binomial_skip = binomial;
            g = eval(node->c);
            binomial_skip = NULL;
        }
        binomial_live = 0;
        env_pop();
    }

    /* Un denominatore di un solo termine si porta nei termini del
     * numeratore; altrimenti non deve contenere t, e divide tutta la somma.
     * Da qui in poi i conti non sono dell'enunciato ma della regola, e le
     * loro divisioni non pongono condizioni. */
    conditions_on = 0;
    Poly pieces = g.num, below = poly_const(num_int(1));
    if (fits && !failure && g.den.count == 1) {
        Term inverse = {num_inv(g.den.term[0].coef), mono_pow(&g.den.term[0].mono, frac_int(-1))};
        pieces = poly_mul(g.num, poly_term(inverse));
    } else if (fits && !failure) {
        below = g.den;
        fits = !poly_has_slack(below);
    }

    /* Un termine alla volta: c, y e la sua forma chiusa. */
    for (int j = 0; fits && !failure && j < pieces.count; j++) {
        Term constant = {pieces.term[j].coef, {0}};
        Rat y = one;
        for (int f = 0; fits && f < pieces.term[j].mono.count; f++) {
            Factor factor = pieces.term[j].mono.factor[f];
            const Atom *a = &atoms[factor.atom];
            if (a->kind == ATOM_POW && mono_exponent(&a->exponent, slack).num != 0) fits = binomial_ratio(factor.atom, factor.exp, step, &y);
            else if (atom_has_slack(factor.atom)) fits = 0;
            else constant.mono = mono_mul(&constant.mono, &(Mono){1, {factor}});
        }
        if (!fits || failure) break;
        Rat c = {poly_term(constant), poly_const(num_int(1))}, plus = binomial_power(rat_add(one, y, 0), upper), closed = plus;
        if (step == 2) {
            /* y qui è la radice: y^2 è il rapporto tra due termini. */
            Rat minus = binomial_power(rat_add(one, y, 1), upper);
            if (y.num.count == 0) { fits = 0; break; }
            closed = rat_div(rat_add(plus, minus, shift), rat_mul(rat_int(2), rat_pow_int(y, shift)));
        }
        total = rat_add(total, rat_mul(c, closed), 0);
    }
    if (fits && !failure) total = rat_div(total, (Rat){below, poly_const(num_int(1))});
    conditions_on = listed;

    /* I termini prima di lower, che la formula conta e la somma no. */
    for (long long k = 0; fits && !failure && k < lower; k++) total = rat_add(total, eval_body(node, rat_int(k)), 1);
    domain_on = domain;
    if (!fits || failure) { failure = saved; return 0; }
    *out = total;
    return 1;
}

/* Ritorna e^{i sign theta}, con sign uguale a +1 o -1.
 *
 * L'angolo theta deve essere un polinomio: una somma di termini q M con q
 * razionale. Poiché e^{i (u + v)} = e^{i u} e^{i v}, il risultato è il
 * prodotto degli atomi e^{i M} elevati a q. Per esempio, con theta = (n+1) x/2
 * = n x/2 + x/2 si ottiene (e^{i n x})^{1/2} (e^{i x})^{1/2}: le formule di
 * addizione di seno e coseno sono già qui dentro. */
Rat exp_i(Rat theta, int sign) {
    Term out;
    out.coef = num_int(1);
    out.mono.count = 0;
    if (!poly_is_one(theta.den)) { fail("angolo con un denominatore che non è un monomio"); return rat_int(0); }
    for (int i = 0; i < theta.num.count; i++) {
        const Term *t = &theta.num.term[i];
        if (t->coef.im.num != 0) { fail("angolo complesso"); return rat_int(0); }
        term_times(&out, atom_pow(BASE_EI, 0, &t->mono), frac_mul(t->coef.re, frac_int(sign)));
    }
    return (Rat){poly_term(out), poly_const(num_int(1))};
}

/* Raccoglie in factor[] i fattori in cui è scritta l'espressione del nodo, e
 * ne aggiorna il numero in *count. Un prodotto o un quoziente danno i fattori
 * dei due operandi; un segno meno dà il fattore -1; una potenza a esponente
 * dispari dà quelli della base. Tutto il resto è un fattore solo, il suo
 * valore: numeratore e denominatore.
 *
 * Una potenza a esponente pari non cambia il segno del prodotto, ma lo
 * annulla dove si annulla la base: se `positive` è diverso da zero si annota
 * a parte che la base non deve essere zero. Con troppi fattori ritorna 0. */
static int sign_factors(const Node *node, Poly *factor, int *count, int positive) {
    if (failure) return 0;
    if (node->kind == N_MUL || node->kind == N_DIV)
        return sign_factors(node->a, factor, count, positive) && sign_factors(node->b, factor, count, positive);
    if (node->kind == N_POW && node->b->kind == N_NUM && node->b->value % 2 == 0) {
        if (positive) require(NEVER_ZERO, eval(node->a).num, "logaritmo di zero");
        return 1;
    }
    if (node->kind == N_POW && node->b->kind == N_NUM) return sign_factors(node->a, factor, count, positive);

    /* Un segno meno, e poi ciò che nega; oppure un fattore così com'è. */
    Rat value = node->kind == N_NEG ? rat_int(-1) : eval(node);
    Poly piece[2] = {value.num, value.den};
    for (int i = 0; i < 2; i++) {
        if (poly_is_one(piece[i])) continue;
        if (*count == MAX_SIGN_FACTORS) return 0;
        factor[(*count)++] = piece[i];
    }
    return node->kind == N_NEG ? sign_factors(node->a, factor, count, positive) : 1;
}

/* Annota che l'argomento di un logaritmo, il nodo `argument` di valore x,
 * deve essere positivo. Il segno di un prodotto si decide meglio fattore per
 * fattore che sul prodotto svolto: di sin(a) cos(b) si sa dire il segno dei
 * due fattori, della somma di quattro esponenziali a cui si riduce no. Per
 * questo la condizione porta i fattori dell'argomento com'è scritto; se sono
 * troppi porta il prodotto di numeratore e denominatore del valore, che ha
 * lo stesso segno. */
static void require_positive(const Node *argument, Rat x) {
    const char *why = "logaritmo di un numero non positivo";
    Poly factor[MAX_SIGN_FACTORS];
    int count = 0;
    if (!conditions_on || failure) return;
    if (sign_factors(argument, factor, &count, 1) && count > 0) require_product(ALWAYS_POSITIVE, factor, count, why);
    else if (!failure) require(ALWAYS_POSITIVE, poly_mul(x.num, x.den), why);
}

/* I valori assoluti del confronto che la tabella dei segni (18p) sta
 * preparando: abs_node[i] è il nodo del valore assoluto numero i, e il bit i
 * di abs_pattern dice se in questo conto il suo argomento va preso con il
 * segno cambiato. Fuori da quei conti abs_count è zero. */
const Node *abs_node[MAX_ABS];
int abs_count;
unsigned abs_pattern;

/* Le radici quadrate del confronto che la tabella dei segni (18p-7) sta
 * preparando: surd_node[i] è un nodo con il radicando numero i (radici con
 * lo stesso radicando scritto sono una sola), surd_letter[i] l'atomo che la
 * rappresenta, surd_inside[i] il radicando come frazione, e surd_value[i]
 * ciò che nei conti prende il posto della radice: la sua lettera, oppure un
 * prodotto di altre lettere quando la radice si ricava da quelle
 * (surd_relate()). Le più interne vengono prima, così un radicando contiene
 * solo le lettere delle radici precedenti. Fuori da quei conti surd_count è
 * zero. */
const Node *surd_node[MAX_SURDS];
int surd_letter[MAX_SURDS];
Rat surd_inside[MAX_SURDS], surd_value[MAX_SURDS];
int surd_count;

/* Il segno di un numero che può contenere radici quadrate di interi. È
 * definita nel capitolo 18.12 (18p), dopo il test di annullamento che le
 * serve; qui la usa il valore assoluto di un numero. */
int number_sign(Rat r, int *side);

/* Gli esponenziali e i logaritmi nella tabella dei segni (18p-8): mentre la
 * tabella prepara un confronto, una potenza con la variabile all'esponente e
 * un logaritmo con la variabile nell'argomento diventano lettere, e sono
 * queste due funzioni a dirlo. Ritornano 1 e mettono in *out ciò che prende
 * il posto del nodo, oppure 0 se il nodo va calcolato come sempre. Sono
 * definite nel capitolo 18.9, con le altre lettere della tabella. */
int exp_letters(const Node *node, Rat *out);
int log_letter(const Node *node, Rat *out);

/* La radice di un prodotto di esponenziali (18p-8): se il radicando r di una
 * radice di indice index è un tale prodotto e la radice si estrae, la mette
 * in *out e ritorna 1. */
int exp_root(Rat r, long long index, Rat *out);

/* Le funzioni goniometriche nella tabella dei segni (18p-11): mentre la
 * tabella prepara un confronto di un enunciato periodico, seno, coseno,
 * tangente e cotangente di a x + b pi diventano frazioni nella lettera
 * t = tan(g x / 2). trig_value() ritorna 1 e mette in *out ciò che prende
 * il posto del nodo, il cui argomento vale argument; 0 se il nodo va
 * calcolato come sempre. È definita nel capitolo 18.9. */
int trig_value(const Node *node, Rat argument, Rat *out);

/* Valuta una chiamata di funzione. */
static Rat eval_call(const Node *node) {
    /* Il logaritmo di un valore assoluto è esattamente ciò che logarithm()
     * calcola, quindi lì il valore assoluto si attraversa. Altrove non c'è
     * ancora una regola per trattarlo. */
    const Node *argument = node->a;
    if ((node->op == FN_LN || node->op == FN_LOG) && argument->kind == N_CALL && argument->op == FN_ABS)
        argument = argument->a;
    int absolute = (argument != node->a);
    Rat letter;

    Rat x = eval(argument);
    switch ((Function)node->op) {
    case FN_FACT:
        return eval_sequence('!', x);

    case FN_BINOM: {
        /* Coefficiente binomiale "x su r".
         *
         * 11i. r intero costante: il prodotto di (x - r + j) / j per j da 1 a
         *      r, cioè x (x-1) ... (x-r+1) / r!. È un polinomio in x e vale
         *      anche quando x < r, dove dà correttamente zero.
         * 11j. r simbolico: x! / (r! (x-r)!), valida per 0 <= r <= x. */
        if (node == binomial_skip) return rat_int(1);  /* 11n: il resto del termine */
        Rat r = eval(node->b);
        long long count;
        if (rat_integer(r, &count)) {
            if (count < 0 || count > MAX_UNROLL) { fail("coefficiente binomiale con indice inferiore non valido"); return rat_int(0); }
            Rat result = rat_int(1);
            for (long long j = 1; j <= count && !failure; j++)
                result = rat_div(rat_mul(result, rat_add(x, rat_int(count - j), 1)), rat_int(j));
            return result;
        }
        Rat below = rat_mul(eval_sequence('!', r), eval_sequence('!', rat_add(x, r, 1)));
        return rat_div(eval_sequence('!', x), below);
    }

    case FN_SIN: case FN_COS: case FN_TAN: case FN_COT: {
        if (trig_value(node, x, &letter)) return letter;

        /* Formule di Eulero: con E = e^{i x},
         *     cos x = (E + 1/E) / 2,    sin x = (E - 1/E) / (2 i).
         * Dividere per 2 i equivale a moltiplicare per -i/2. */
        Rat forward = exp_i(x, 1), backward = exp_i(x, -1);
        Rat half = rat_div(rat_int(1), rat_int(2));
        Rat minus_half_i = {poly_const((Num){frac_int(0), (Frac){-1, 2}}), poly_const(num_int(1))};
        Rat cosine = rat_mul(rat_add(forward, backward, 0), half);
        Rat sine = rat_mul(rat_add(forward, backward, 1), minus_half_i);
        if (node->op == FN_SIN) return sine;
        if (node->op == FN_COS) return cosine;
        return node->op == FN_TAN ? rat_div(sine, cosine) : rat_div(cosine, sine);
    }

    case FN_ROOT: {
        /* La radice di indice r è la potenza 1/r. */
        long long index;
        if (!rat_integer(eval(node->b), &index) || index < 2) { fail("indice di radice non intero o minore di 2"); return rat_int(0); }

        /* Nella tabella dei segni una radice quadrata resta un simbolo. Lì la
         * variabile è un numero reale qualsiasi, e le semplificazioni di
         * fractional_power(), pensate per quantità positive, non valgono: la
         * radice di x^2 non è x. */
        if (exp_root(x, index, &letter)) return letter;
        for (int i = 0; i < surd_count && index == 2; i++)
            if (node_equal(surd_node[i]->a, node->a)) return surd_value[i];

        /* 11p. La radice m-esima di una potenza w^k scritta così: con m
         * dispari è w^{k/m} per ogni w reale (11o); con m pari e k dispari
         * è definita dove w^k >= 0, cioè dove w >= 0, e lì vale w^{k/m}. Con
         * m e k pari no: la radice quadrata di w^2 è |w|, non w, e resta la
         * regola di sempre. Serve perché la radice cubica di (x^3 + 1)^2 e
         * il quadrato di quella di x^3 + 1 siano lo stesso numero anche per
         * il conto: svolta la potenza, i due radicandi non si riconoscono. */
        const Node *power_node = node->a;
        if (power_node->kind == N_POW && power_node->b->kind == N_NUM && power_node->b->value >= 1 && power_node->b->value <= MAX_POWER &&
            (index % 2 || power_node->b->value % 2)) {
            Frac q = frac_make(power_node->b->value, index);
            Rat w = eval(power_node->a);
            return q.den == 1 ? rat_pow_int(w, q.num) : fractional_power(w, q, index % 2);
        }
        return fractional_power(x, (Frac){1, index}, index % 2);
    }

    case FN_LN:
        if (log_letter(node, &letter)) return letter;
        if (!absolute) require_positive(argument, x);
        return absolute ? logarithm(x) : logarithm_of_positive(x);

    case FN_LOG: {
        /* Cambio di base: il logaritmo di x in base b è ln x / ln b. */
        if (!node->b) { fail("logaritmo senza base: scrivere \\ln oppure \\log_{b}"); return rat_int(0); }
        if (log_letter(node, &letter)) return letter;
        if (!absolute) require_positive(argument, x);
        Rat above = absolute ? logarithm(x) : logarithm_of_positive(x);
        Rat below = eval(node->b);
        require_positive(node->b, below);
        return rat_div(above, logarithm_of_positive(below));
    }

    case FN_ARCTAN:
        return arctangent(x);

    case FN_ARCCOT:
        /* Con l'arcocotangente a valori in (0, pi), come nei libri di
         * scuola, arccot u = pi/2 - arctan u per ogni u reale: i due membri
         * sono continui, hanno la stessa cotangente, e stanno tutti e due
         * in (0, pi), dove la cotangente è iniettiva. */
        return rat_add(rat_div(rat_atom(atom_var(VAR_PI)), rat_int(2)), arctangent(x), 1);

    case FN_ARCSIN: case FN_ARCCOS:
        /* Non c'è una forma esatta che valga in tutto [-1, 1]: arcsin u =
         * arctan(u / sqrt(1 - u^2)) perde i due estremi, e un'espressione
         * che risultasse non definita dove lo è sbaglierebbe la tabella dei
         * segni. Di queste funzioni si calcolano le derivate (27f), che non
         * le contengono, e i valori con gli intervalli (capitolo 24). */
        fail("arcoseno e arcocoseno non hanno una forma per i conti esatti");
        return rat_int(0);

    case FN_ABS: {
        /* Di un numero reale il valore assoluto si calcola. Di un'espressione
         * no, perché |x| non è una funzione razionale di x: vale x oppure -x
         * secondo il segno. La tabella dei segni (18p) fa il conto una volta
         * per ogni scelta, e dice quale con abs_pattern. */
        Num value;
        int side;
        if (rat_number(x, &value) && value.im.num == 0) return value.re.num < 0 ? rat_add(rat_int(0), x, 1) : x;

        /* Il caso scelto per questo valore assoluto. Nel conto di
         * un'uguaglianza dove i due membri sono definiti (11q), il valore
         * scelto, x oppure -x, è >= 0 nei punti di quel caso: un fatto. */
        for (int i = 0; i < abs_count; i++)
            if (abs_node[i] == node || node_equal(abs_node[i], node)) {
                Rat chosen = (abs_pattern >> i & 1) ? rat_add(rat_int(0), x, 1) : x;
                domain_note(chosen);
                return chosen;
            }

        /* 11q-3. Un segno che dicono i fatti del dominio. */
        int known = domain_sign(x);
        if (known) return known < 0 ? rat_add(rat_int(0), x, 1) : x;

        /* Un numero con radici quadrate: il segno si trova stringendolo tra
         * due razionali (number_sign(), 18p). */
        if (number_sign(x, &side)) return side < 0 ? rat_add(rat_int(0), x, 1) : x;
        if (!failure) fail("valore assoluto non ancora supportato");
        return rat_int(0);
    }
    }
    return rat_int(0);
}

/* Ritorna 1 se il numero u divide il numero v, cioè se v è u per un numero
 * intero (17n): zero divide solo zero, e un altro numero divide v quando il
 * quoziente è intero. Vale per i razionali come è scritta: 1/2 divide 3. */
int number_divides(Num u, Num v) {
    if (u.im.num != 0 || v.im.num != 0) return 0;
    if (u.re.num == 0) return v.re.num == 0;
    return frac_div(v.re, u.re).den == 1;
}

/* 11v. LE APPLICAZIONI DEFINITE PER CASI: QUALE CASO VALE
 *
 * f(t), con f definita per casi (17s), vale il valore del caso la cui
 * condizione vale in t. Quando t è un numero il caso si trova calcolando le
 * condizioni, e si prende il primo che vale: che i casi che valgono insieme
 * diano lo stesso numero lo ha dimostrato la regola 18v-6, prima di ogni
 * altra cosa, e lo ricontrolla map_holds_on_sample() (capitolo 19).
 *
 * Quando t contiene le variabili generiche di una dimostrazione, calcolare
 * non basta: il caso va dimostrato, per tutti i loro valori. Lo fa la regola
 * 18v-1, che annota la sua scelta in case_choice[]; qui la si legge
 * soltanto. Se manca, il conto fallisce con CASE_UNDECIDED, e
 * l'applicazione resta annotata in undecided_*: chi cerca una dimostrazione
 * ne ricava che cosa distinguere (18v-2) o quali casi provare (18v-3).
 */

/* Le scelte valide in questo momento, dalla più vecchia. Chi le aggiunge le
 * toglie quando ha finito, riportando il contatore dov'era. */
CaseChoice case_choice[MAX_CASE_CHOICES];
int case_choice_count;

/* Il motivo del fallimento di un conto che ha incontrato un'applicazione
 * definita per casi senza un caso scelto. Ha un nome perché chi cerca una
 * dimostrazione lo riconosce: non è un errore dell'enunciato. */
const char *const CASE_UNDECIDED = "un'applicazione definita per casi è calcolata in un punto in cui il caso non è stabilito";

/* L'ultima applicazione che ha fatto fallire un conto con CASE_UNDECIDED: la
 * sua definizione, il suo nodo e il valore dell'argomento. */
const Map *undecided_map;
const Node *undecided_node;
Rat undecided_argument;

/* Ritorna 1 se a e b sono scritte allo stesso modo, termine per termine. */
int rat_same(Rat a, Rat b) { return poly_equal(a.num, b.num) && poly_equal(a.den, b.den); }

/* Calcola con i numeri la condizione c di un caso, in cui ogni variabile ha
 * un numero per valore: ritorna 1 se è vera, 0 se è falsa, -1 se un membro
 * non è un numero reale o il conto non riesce. */
int condition_computed(const Formula *c) {
    Num u, v;
    if (c->kind == F_NOT) {
        int inner = condition_computed(c->a);
        return inner < 0 ? -1 : !inner;
    }
    if (c->kind == F_AND || c->kind == F_OR) {
        int x = condition_computed(c->a), y = condition_computed(c->b);
        if (x < 0 || y < 0) return -1;
        return c->kind == F_AND ? x && y : x || y;
    }
    int numbers = rat_number(eval(c->left), &u) && u.im.num == 0;
    if (c->kind != F_IN) numbers = numbers && rat_number(eval(c->right), &v) && v.im.num == 0;
    if (failure || !numbers) return -1;
    switch (c->kind) {
    case F_EQUAL:    return frac_cmp(u.re, v.re) == 0;
    case F_DISTINCT: return frac_cmp(u.re, v.re) != 0;
    case F_LESS:     return frac_cmp(u.re, v.re) < 0;
    case F_LESS_EQ:  return frac_cmp(u.re, v.re) <= 0;
    case F_DIVIDES:  return number_divides(u, v) != c->swapped;
    case F_IN:       return numbers_contain(&c->numbers, u.re) != c->swapped;
    default:         return -1;
    }
}

/* Calcola con i numeri quale caso di map vale nel punto argument: ritorna il
 * primo che vale, -1 se nessuno vale, -2 se il punto non è un numero o una
 * condizione non si calcola, perché nomina anche una variabile generica,
 * come un parametro (17s). */
int case_computed(const Map *map, Rat argument) {
    Num t;
    if (!rat_number(argument, &t) || t.im.num != 0) return -2;
    for (int i = 0; i < map->cases && !failure; i++) {
        env_push(map->parameter, argument);
        int holds = condition_computed(map->piece[i].when);
        env_pop();
        if (holds) return holds > 0 ? i : -2;
    }
    return failure ? -2 : -1;
}

/* Ritorna il caso di map che vale per l'applicazione node, il cui argomento
 * vale argument, come descritto in testa al paragrafo; -1, con fail(), se
 * non lo si sa. */
static int case_of(const Map *map, const Node *node, Rat argument) {
    int computed = case_computed(map, argument);
    if (failure) return -1;
    if (computed >= 0) return computed;
    if (computed == -1) {
        fail_undefined("nessun caso della definizione vale in questo punto");
        return -1;
    }
    for (int i = case_choice_count - 1; i >= 0; i--)
        if (case_choice[i].node == node && rat_same(case_choice[i].argument, argument)) return case_choice[i].piece;
    undecided_map = map;
    undecided_node = node;
    undecided_argument = argument;
    fail(CASE_UNDECIDED);
    return -1;
}

/* Ritorna il valore del nodo con le variabili legate attuali. In caso di
 * errore `failure` è impostato e il valore non ha significato. */
Rat eval(const Node *node) {
    /* Dopo un errore il risultato verrà scartato: ci si ferma subito, anche
     * per non svolgere somme con estremi privi di senso. */
    if (failure) return rat_int(0);

    switch (node->kind) {
    case N_NUM:
        return rat_int(node->value);
    case N_VAR: {
        const Rat *bound = env_lookup(node->name);
        return bound ? *bound : rat_atom(atom_var(node->name));
    }
    case N_SEQ:
        return eval_sequence(node->name, eval(node->a));
    case N_NEG:
        return rat_add(rat_int(0), eval(node->a), 1);
    case N_BIGOP:
        return eval_bigop(node);
    case N_CALL:
        return eval_call(node);
    case N_APPLY: {
        /* f(a) è la regola di f calcolata con la sua variabile legata ad a.
         * La regola non contiene altre lettere (lo controlla il capitolo 17),
         * quindi le variabili legate in questo momento non la toccano. */
        const Map *map = map_find(node->name);
        if (!map || (!map->body && !map->cases)) { fail("applicazione senza la regola che la definisce"); return rat_int(0); }

        /* Gli argomenti si calcolano prima di legare le variabili della
         * regola: in (a \ast b) \ast c, con la regola scritta in a e b,
         * la a dell'argomento è quella dell'enunciato. Per una definizione
         * per casi la regola è il valore del caso che vale (11v). */
        Rat first = eval(node->a);

        /* 17s. L'iterata f^{m}(a): con f^{c} = f, è f applicata m - c + 1
         * volte. Si calcola solo con m un numero; con m una lettera la
         * dimostra il capitolo 26 (26c), come una successione. */
        if (node->c) {
            long long m;
            if (!rat_integer(eval(node->c), &m)) { fail("un'iterata con l'esponente che non è un numero si dimostra solo per induzione"); return rat_int(0); }
            if (map->iterates != 3 || map->iterate_from != map->step_from || map->binary || m < map->iterate_from ||
                m - map->iterate_from >= MAX_UNROLL) {
                fail("un'iterata fuori dagli indici per cui le ipotesi la definiscono");
                return rat_int(0);
            }
            Node once = *node;
            once.c = NULL;
            for (long long k = map->iterate_from; k <= m && !failure; k++) {
                env_push(VAR_ITERATE, first);
                Node at = {N_VAR, 0, VAR_ITERATE, 0, NULL, NULL, NULL};
                once.a = &at;
                first = eval(&once);
                env_pop();
            }
            return first;
        }
        const Node *body = map->body;
        if (map->cases) {
            int piece = case_of(map, node, first);
            if (piece < 0) return rat_int(0);
            body = map->piece[piece].value;
        }
        if (map->binary) {
            Rat second = eval(node->b);
            env_push(map->parameter, first);
            env_push(map->parameter2, second);
        } else {
            env_push(map->parameter, first);
        }
        Rat value = eval(body);
        if (map->binary) env_pop();
        env_pop();
        return value;
    }
    case N_DERIV:
        /* Un segno di derivata che nessuno ha espanso (27j): non ha un
         * valore, e non va letto come nient'altro. */
        fail("un segno di derivata dentro un'espressione che il programma non ha calcolato");
        return rat_int(0);
    default:
        break;
    }

    /* Nella tabella dei segni una potenza con la variabile all'esponente è
     * un prodotto di lettere (18p-8). */
    Rat letters;
    if (node->kind == N_POW && exp_letters(node, &letters)) return letters;

    /* Operatori binari. I due operandi vanno valutati in istruzioni separate:
     * come argomenti della stessa chiamata il C non ne fisserebbe l'ordine, e
     * l'ordine decide con quale estremo nasce un atomo (vedi eval_bigop()). */
    Rat a = eval(node->a);
    Rat b = eval(node->b);
    switch (node->kind) {
    case N_ADD: return rat_add(a, b, 0);
    case N_SUB: return rat_add(a, b, 1);
    case N_MUL: return rat_mul(a, b);
    case N_DIV: return rat_div(a, b);
    default:    return power(a, b);
    }
}

/* =============================================================================
 * 12. TEST DI ANNULLAMENTO
 * ============================================================================
 *
 * "Questo polinomio è zero?" è la domanda a cui si riduce ogni dimostrazione.
 * Per quasi tutti gli atomi la risposta è nella forma canonica: è zero se non
 * ha termini. Due famiglie di atomi però soddisfano identità che la forma
 * canonica non vede, e vanno applicate qui.
 *
 *   12a. Radici. L'atomo "u preso come lettera", con u un polinomio, compare
 *        con esponenti frazionari: la radice quadrata di u è u^{1/2}. Ma
 *        u^1 non è una lettera nuova: è il polinomio u. Quindi di ogni
 *        esponente si separa la parte intera, che torna a essere il polinomio.
 *
 *   12b. Logaritmi. Una combinazione c1 ln|u1| + ... + ck ln|uk| con
 *        coefficienti interi è il logaritmo di |u1^c1 ... uk^ck|, quindi è
 *        zero quando quel prodotto vale 1 oppure -1. E quest'ultima è
 *        un'uguaglianza tra frazioni, senza più logaritmi.
 *
 *   12c. Arcotangenti. Per u reale, arctan(u) è l'argomento, cioè l'angolo,
 *        del numero complesso 1 + i u. Gli argomenti di un prodotto si
 *        sommano, quindi c1 arctan(u1) + ... + ck arctan(uk), con coefficienti
 *        interi, è l'argomento di Z = (1 + i u1)^c1 ... (1 + i uk)^ck, a meno
 *        di multipli di 2 pi. Se Z è un numero reale positivo il suo
 *        argomento è zero, e la combinazione è un multiplo di 2 pi; se
 *        inoltre è piccola in valore assoluto, quel multiplo è zero.
 *
 * Le tre regole sono vere identità, quindi un "sì" resta una dimostrazione.
 * Non sono complete: uno zero che dipende da altre identità (per esempio tra
 * radici di polinomi non scomposti) riceve un "no", e l'enunciato resta NON
 * DIMOSTRATO.
 *
 *   12d. Dove i due membri sono definiti. Il test di sempre, su L - R
 *        calcolata con i fatti del dominio (11q): vanishes_where_defined().
 *        Un "sì" vuol dire L = R in ogni punto in cui i due membri sono
 *        definiti, e non altrove: lo usano solo le uguaglianze che
 *        affermano questo, le derivate (27a) e le primitive (30a).
 */

/* Ritorna un polinomio che è zero se e solo se lo è p, in cui ogni atomo
 * "polinomio u preso come lettera" compare con esponente in [0, 1) (12a).
 *
 * Per un atomo x di base u: se k è il più piccolo tra le parti intere degli
 * esponenti di x (contando zero dove x manca), si moltiplica tutto p per
 * x^{-k}, che non cambia l'essere zero, e poi in ogni termine si sostituisce
 * la parte intera j dell'esponente con il polinomio u^j. I termini con la
 * stessa parte intera si raccolgono, e le potenze di u si moltiplicano con lo
 * schema di Horner: ((P_top u + P_{top-1}) u + ...) + P_k.
 *
 * Si procede dall'atomo creato per ultimo al primo: la base di un atomo
 * contiene solo atomi creati prima di lui, quindi sostituirla può far
 * comparire solo esponenti ancora da sistemare, mai già sistemati.
 *
 * Con keep_value diverso da zero il risultato deve avere anche lo stesso
 * valore di p, non solo lo stesso essere zero (serve a 11q-4): un atomo con
 * una parte intera negativa, che chiederebbe di moltiplicare per x^{-k}, si
 * lascia com'è. Con k = 0 la moltiplicazione non c'è, e la sostituzione di
 * u^j al posto di x^j è un'identità dove la radice è definita. */
static Poly poly_reduce_radicals(Poly p, int keep_value) {
    for (int x = atom_count - 1; x >= 0 && !failure; x--) {
        const Atom *atom = &atoms[x];
        if (atom->kind != ATOM_POW || atom->base != BASE_POLY || atom->exponent.count != 0) continue;

        /* Intervallo delle parti intere degli esponenti di x. */
        long long low = 0, high = 0;
        for (int i = 0; i < p.count; i++) {
            long long whole = frac_floor(mono_exponent(&p.term[i].mono, x));
            if (whole < low) low = whole;
            if (whole > high) high = whole;
        }
        if ((low == 0 && high == 0) || (keep_value && low < 0)) continue;
        if (high - low > MAX_POWER) { fail("esponente di una radice troppo grande"); break; }

        /* Horner, dalla parte intera più alta alla più bassa. */
        Poly result = poly_const(num_int(0));
        for (long long whole = high; whole >= low; whole--) {
            Term *buffer = terms_alloc(p.count);
            if (!buffer && p.count) return p;
            int used = 0;
            for (int i = 0; i < p.count; i++) {
                Term t = p.term[i];
                Frac e = mono_exponent(&t.mono, x);
                if (frac_floor(e) != whole) continue;
                t.mono = mono_with_exponent(&t.mono, x, frac_add(e, frac_int(-whole)));
                buffer[used++] = t;
            }
            Poly same = poly_finish(buffer, p.count, used);
            result = poly_add(poly_mul(result, base_polys[atom->id]), same, 0);
        }
        p = result;
    }
    return p;
}

/* Ritorna, come frazione, la base u dell'atomo ln|u| di indice atom. */
static Rat ln_base(int atom) {
    const Atom *a = &atoms[atom];
    if (a->base == BASE_PRIME) return rat_int(a->id);
    if (a->base == BASE_ATOM) return rat_atom((int)a->id);
    return (Rat){base_polys[a->id], poly_const(num_int(1))};
}

/* Ritorna 1 se p, non nullo, è una combinazione di logaritmi che vale zero
 * per la regola 12b.
 *
 * Ogni termine deve contenere un solo atomo LN, al primo grado. Il resto del
 * monomio è il suo "cofattore": i termini con lo stesso cofattore M formano un
 * gruppo M (c1 ln|u1| + ... + ck ln|uk|), e p è zero se lo è ogni gruppo.
 * I coefficienti razionali si rendono interi moltiplicando il gruppo per il
 * minimo comune multiplo dei denominatori. */
static int log_combination_vanishes(Poly p) {
    int *log_atom = arena_alloc((size_t)p.count * sizeof(int));
    Mono *cofactor = arena_alloc((size_t)p.count * sizeof(Mono));
    if (!log_atom || !cofactor) return 0;

    /* Separa in ogni termine l'atomo LN dal cofattore. */
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        log_atom[i] = -1;
        for (int f = 0; f < t->mono.count; f++) {
            if (atoms[t->mono.factor[f].atom].kind != ATOM_LN) continue;
            if (log_atom[i] >= 0 || t->mono.factor[f].exp.num != 1 || t->mono.factor[f].exp.den != 1) return 0;
            log_atom[i] = t->mono.factor[f].atom;
        }
        if (log_atom[i] < 0 || t->coef.im.num != 0) return 0;
        cofactor[i] = mono_with_exponent(&t->mono, log_atom[i], frac_int(0));
    }

    /* Un gruppo alla volta: il primo termine non ancora trattato e tutti
     * quelli con il suo stesso cofattore. log_atom[j] = -1 segna i trattati. */
    for (int i = 0; i < p.count; i++) {
        if (log_atom[i] < 0) continue;

        /* Minimo comune multiplo dei denominatori dei coefficienti. */
        long long scale = 1;
        for (int j = i; j < p.count; j++) {
            if (log_atom[j] < 0 || mono_cmp(&cofactor[j], &cofactor[i]) != 0) continue;
            long long den = p.term[j].coef.re.den;
            scale = scale / (long long)gcd128(scale, den) * den;
            if (scale > MAX_POWER) return 0;
        }

        /* Il prodotto delle basi, ognuna elevata al proprio coefficiente. */
        Rat product = rat_int(1);
        for (int j = p.count - 1; j >= i; j--) {
            if (log_atom[j] < 0 || mono_cmp(&cofactor[j], &cofactor[i]) != 0) continue;
            long long e = p.term[j].coef.re.num * (scale / p.term[j].coef.re.den);
            product = rat_mul(product, rat_pow_int(ln_base(log_atom[j]), e));
            log_atom[j] = -1;
        }
        if (failure) return 0;

        /* Il gruppo è zero se il prodotto vale 1 oppure -1. */
        if (poly_reduce_radicals(poly_add(product.num, product.den, 1), 0).count != 0 &&
            poly_reduce_radicals(poly_add(product.num, product.den, 0), 0).count != 0)
            return 0;
    }
    return 1;
}

/* Ritorna 1 se p, non nullo, è una combinazione di arcotangenti che vale zero
 * per la regola 12c.
 *
 * Come per i logaritmi, ogni termine deve contenere un solo "angolo" al primo
 * grado, e i termini si raggruppano per cofattore. Un angolo è un atomo ATAN
 * oppure pi greco, che si riscrive come 4 arctan(1).
 *
 * Per un gruppo c1 arctan(u1) + ... + ck arctan(uk), con i coefficienti resi
 * interi e uj = pj/qj:
 *
 *   - Il segno di Z. Invece di dividere, si moltiplica per i coniugati:
 *     Z è un reale positivo esattamente quando lo è
 *
 *         W = prodotto dei (1 + i sj uj)^|cj|,   sj = segno di cj,
 *
 *     perché W è Z per il quadrato del modulo dei fattori a esponente
 *     negativo. Scrivendo 1 + i sj uj = (qj + i sj pj)/qj, W è la frazione
 *     V/Q con V = prodotto dei (qj + i sj pj)^|cj| e Q = prodotto dei
 *     qj^|cj|. Si chiede che V non abbia parte immaginaria e che V Q sia
 *     evidentemente positivo: V e Q hanno allora lo stesso segno.
 *
 *   - La grandezza. Ogni arcotangente è minore di pi/2 in valore assoluto, e
 *     arctan(1) vale esattamente pi/4. Contando 2 per ogni arcotangente e 1
 *     per ogni arctan(1), se il totale pesato con |cj| non supera 8 la
 *     combinazione è minore di 8 * pi/4 = 2 pi in valore assoluto: l'unico
 *     multiplo di 2 pi possibile è zero. Serve almeno un'arcotangente diversa
 *     da arctan(1), altrimenti la disuguaglianza non sarebbe stretta. */
static int arctan_combination_vanishes(Poly p) {
    int pi = atom_var(VAR_PI);
    int *angle = arena_alloc((size_t)p.count * sizeof(int));
    Mono *cofactor = arena_alloc((size_t)p.count * sizeof(Mono));
    if (!angle || !cofactor) return 0;

    /* Separa in ogni termine l'angolo dal cofattore. */
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        angle[i] = -1;
        for (int f = 0; f < t->mono.count; f++) {
            int atom = t->mono.factor[f].atom;
            if (atoms[atom].kind != ATOM_ATAN && atom != pi) continue;
            if (angle[i] >= 0 || t->mono.factor[f].exp.num != 1 || t->mono.factor[f].exp.den != 1) return 0;
            angle[i] = atom;
        }
        if (angle[i] < 0 || t->coef.im.num != 0) return 0;
        cofactor[i] = mono_with_exponent(&t->mono, angle[i], frac_int(0));
    }

    /* Un gruppo alla volta, come in log_combination_vanishes(). */
    for (int i = 0; i < p.count; i++) {
        if (angle[i] < 0) continue;

        /* Coefficienti interi: minimo comune multiplo dei denominatori, dopo
         * aver contato pi greco come 4 arctan(1). */
        long long scale = 1;
        for (int j = i; j < p.count; j++) {
            if (angle[j] < 0 || mono_cmp(&cofactor[j], &cofactor[i]) != 0) continue;
            Frac c = frac_mul(p.term[j].coef.re, frac_int(angle[j] == pi ? 4 : 1));
            scale = scale / (long long)gcd128(scale, c.den) * c.den;
            if (scale > 8) return 0;
        }

        /* V, Q e il controllo sulla grandezza. */
        Poly v = poly_const(num_int(1)), q = poly_const(num_int(1));
        long long weight = 0;
        int proper = 0;
        for (int j = p.count - 1; j >= i; j--) {
            if (angle[j] < 0 || mono_cmp(&cofactor[j], &cofactor[i]) != 0) continue;
            int unit = (angle[j] == pi);
            Frac c = frac_mul(p.term[j].coef.re, frac_int(unit ? 4 * scale : scale));
            long long times = c.num < 0 ? -c.num : c.num;
            Rat u = unit ? rat_int(1) : atan_args[atoms[angle[j]].id];
            angle[j] = -1;
            weight += times * (unit ? 1 : 2);
            if (!unit) proper = 1;
            if (weight > 8) return 0;

            /* Il fattore q + i s p, moltiplicato |c| volte. */
            Num turn = {frac_int(0), frac_int(c.num < 0 ? -1 : 1)};
            Poly factor = poly_add(u.den, poly_mul(poly_const(turn), u.num), 0);
            for (long long k = 0; k < times; k++) {
                v = poly_mul(v, factor);
                q = poly_mul(q, u.den);
            }
        }
        if (failure || !proper) return 0;

        /* V reale, e V Q positivo. */
        for (int k = 0; k < v.count; k++)
            if (v.term[k].coef.im.num != 0) return 0;
        if (!poly_is_positive(poly_mul(v, q))) return 0;
    }
    return 1;
}

/* Ritorna 1 se p è zero, tenendo conto delle identità 12a, 12b e 12c. Un
 * errore durante il conto (in `failure`) vale come "no". */
int poly_vanishes(Poly p) {
    p = poly_reduce_radicals(p, 0);
    if (failure) return 0;
    return p.count == 0 || log_combination_vanishes(p) || arctan_combination_vanishes(p);
}

/* Ritorna L - R per l'enunciato, con la variabile di induzione legata a n e i
 * parametri legati ai valori del punto in uso, se ce n'è uno. */
Rat difference(const Statement *statement, Rat n) {
    env_count = 0;
    library_depth = 0;

    /* I parametri vanno legati per primi: env_varies() li riconosce dal posto. */
    for (int i = 0; i < point_count; i++) env_push(point_name[i], rat_frac(point_value[i]));
    env_push(induction_var, n);
    Rat left = eval(statement->lhs);
    Rat right = eval(statement->rhs);
    env_count = 0;
    return rat_add(left, right, 1);
}

/* 12d. IL TEST DOVE I DUE MEMBRI SONO DEFINITI
 *
 * Ritorna 1 se L - R, calcolata come in difference(), si riduce a zero con i
 * fatti del dominio (11q): allora L = R in ogni punto in cui i due membri
 * sono definiti (e, in un caso dei valori assoluti di 27a, valgono i segni
 * del caso). È il test di annullamento delle uguaglianze che si affermano
 * così, e solo di quelle (vedi "Perché solo lì", in 11q): lo chiamano 27a,
 * con la rilettura della derivata calcolata (27k), e 30a.
 *
 * source, se non è NULL, è un'espressione definita in ogni punto in cui
 * l'uguaglianza si afferma, anche se non ne è un membro: la funzione di cui
 * L è la derivata (27a), che deve essere definita dove è derivabile; la
 * primitiva F di cui L è F' (30a), che l'enunciato considera solo dove è
 * definita. Le sue radici e i suoi logaritmi danno fatti come quelli dei
 * membri, ed è lei a darli quando le regole li perdono: la derivata di
 * \ln(x + 3) è \frac{1}{x + 3}, definita anche per x < -3. Si calcola una
 * volta, per prima, solo per i fatti: un errore nel suo conto (un arcoseno,
 * che il conto esatto non ha) non riguarda l'uguaglianza, e i fatti trovati
 * prima dell'errore valgono lo stesso.
 *
 * I fatti si annotano mentre si calcola, e uno trovato in un membro può
 * servire a un'espressione calcolata prima: per questo il conto si rifà,
 * ogni volta con tutti i fatti trovati nelle volte precedenti, finché ne
 * compaiono di nuovi e la differenza non si è ridotta a zero, al più
 * DOMAIN_PASSES volte. Un conto che fallisce (la radice di una frazione i
 * cui termini non hanno segno noto, per esempio) si ferma al primo membro, e
 * i fatti dell'altro non arrivano: per questo le volte dispari calcolano
 * R - L, con il secondo membro per primo, che si annulla quando si annulla
 * L - R. Dopo un conto riuscito senza fatti nuovi rifarlo non cambierebbe
 * nulla; dopo uno fallito si prova almeno l'altro ordine. Se fallisce anche
 * l'ultima volta, `failure` resta impostato. All'uscita i fatti sono spenti
 * e dimenticati: non arrivano a nessun altro conto.
 *
 * Le condizioni di esistenza (capitolo 7) restano spente per tutto il test:
 * sono ciò che 13c deve controllare, e i fatti, che le suppongono vere,
 * cambierebbero quelle annotate. */
int vanishes_where_defined(const Statement *statement, const Node *source, Rat n) {
    const char *was = failure;
    Statement turned = {statement->rhs, statement->lhs, statement->relation};
    int vanishes = 0, listed = conditions_on;
    conditions_on = 0;
    domain_on = 1;
    domain_fact_count = 0;
    if (source) {
        Statement facts_only = {(Node *)source, node_num(0), REL_EQ};
        difference(&facts_only, n);
    }
    for (int pass = 0; pass < DOMAIN_PASSES && !vanishes; pass++) {
        int known = domain_fact_count;
        failure = was;
        Rat gap = difference(pass % 2 ? &turned : statement, n);
        vanishes = !failure && poly_vanishes(gap.num);
        if (domain_fact_count == known && (pass > 0 || !failure)) break;
    }
    domain_on = 0;
    domain_fact_count = 0;
    conditions_on = listed;
    return vanishes;
}
