/* =============================================================================
 * 19. QUANTIFICATORI: VERIFICA INDIPENDENTE E VERDETTO
 * ============================================================================
 *
 * Verifica indipendente. Il capitolo 18 ragiona con i polinomi: scompone,
 * risolve, studia segni. Qui lo stesso enunciato viene ricontrollato senza
 * algebra, calcolando con i numeri: ogni "per ogni" si prova sui primi
 * elementi dell'insieme, ogni "esiste" con il valore scelto dalla
 * dimostrazione (quello del caso giusto, se la dimostrazione è per casi sul
 * resto), e ogni confronto è un confronto tra due numeri. Se la
 * dimostrazione dice x = (y + 1)/(y - 1), per ogni y del campione si calcola
 * quel numero, si guarda se sta nell'insieme e se soddisfa la condizione.
 *
 * Come per gli insiemi (capitolo 16) non è una seconda dimostrazione, perché
 * il campione è finito: è un controllo contro gli errori del programma. Se
 * non conferma la dimostrazione, il verdetto non viene emesso.
 *
 * I valori da provare. I primi elementi di un insieme non bastano quando
 * l'enunciato chiede qualcosa di raro. In "per ogni x, se esiste k con x =
 * k^2 + 7 allora ..." nessuno dei primi interi soddisfa l'ipotesi, e
 * un'implicazione con l'ipotesi falsa è vera qualunque cosa dica la tesi:
 * una verifica così sarebbe una prova su strada fatta solo nei giorni di
 * sole. Perciò ogni quantificatore prova anche i valori che le condizioni
 * gli impongono (sample_equations(), sample_candidates()): da alpha x +
 * beta = 0 il valore -beta/alpha; e se l'uguaglianza contiene la lettera k
 * di un "esiste" più interno, per ogni k del campione il valore di x che la
 * rende vera. Così x = k^2 + 7 dà x = 7, 8, 11, 16, ..., e l'ipotesi vale
 * per costruzione. Divisibilità e appartenenza si leggono con la loro
 * definizione: n | a - b dice a - b = q n con q intero, e q si sceglie. E
 * tra i valori di una variabile razionale ce n'è sempre uno che non è
 * intero (check_sample()), anche quando le variabili sono tante e i valori
 * pochi.
 *
 * I valori scelti da 18u. Riuscita la regola 18u, i valori annotati nei
 * nodi vengono dimenticati (vedi 18u): la verifica dell'enunciato ricalcola
 * ogni "esiste" com'è scritto, e del valore scelto dalla dimostrazione non
 * direbbe nulla. Lo ricontrolla record_holds(), con ciò che 18u-3 ha
 * annotato in witness_records[]: dove le ipotesi valgono, il valore deve
 * stare nel suo insieme e rendere vera la condizione. Le variabili generiche
 * si scelgono anche lì in modo che le ipotesi valgano: prima un numero per
 * ogni testimone nominato da 18u-1, poi le altre ricavate dalle ipotesi.
 * È un conto con i numeri, indipendente dall'identità tra polinomi con cui
 * 18s ha giustificato il passo.
 *
 * Quante prove servono. Una verifica che non ha mai trovato vere le ipotesi
 * non ha controllato nulla. Se la dimostrazione ha preso un'ipotesi "esiste"
 * con il suo testimone (18u-1), la verifica dell'enunciato deve aver trovato
 * vera la tesi di un'implicazione, con l'ipotesi vera, almeno MIN_SATISFIED
 * volte; e ogni valore annotato da 18u-3 deve essere stato provato su almeno
 * MIN_SATISFIED scelte che soddisfano le ipotesi. Altrimenti il verdetto è
 * NON DIMOSTRATO, e il motivo lo dice. Così resta senza verdetto anche un
 * enunciato vero perché le sue ipotesi non valgono mai, come "se x^2 = 2k^2
 * + 3 allora ...": nessuno ha controllato che non valgano, e un'ipotesi che
 * la verifica non sa soddisfare non è per questo impossibile.
 *
 * Perché ne basta una. Una soglia più alta sembrerebbe più prudente, ma ci
 * sono ipotesi che valgono in un punto solo: una relazione che contiene solo
 * le coppie (1, v) è antisimmetrica, e "(x, y) e (y, x) nella relazione"
 * vale solo per x = y = 1. Lì una prova è tutta la verifica possibile, e
 * una soglia di quattro ha tolto il verdetto a tre enunciati di questo tipo
 * generati da fuzz_relations.py, uno dimostrato e due smentiti, tutti e tre
 * giustamente. Dove le soluzioni sono tante, le
 * prove sono tante anche loro, perché i valori si ricavano dalle ipotesi
 * (vedi "I valori da provare").
 */

/* Mette in *out il valore r con ogni variabile legata in questo momento
 * sostituita dal suo valore, una per volta. Ritorna 0 se un conto non
 * riesce. */
static int substituted(Rat r, Rat *out) {
    for (int i = 0; i < env_count && !failure; i++) {
        Poly num, den;
        int x = atom_var(env_at(i)->name);
        if (!rat_polynomials(r, &num, &den)) return 0;
        r = rat_div(poly_substitute(num, x, env_at(i)->value), poly_substitute(den, x, env_at(i)->value));
    }
    *out = r;
    return !failure;
}

/* Calcola un valore scelto dalla dimostrazione, chosen, ora che le variabili
 * da cui dipende sono legate a numeri. Mette il numero in *value e ritorna
 * 1; ritorna 0 se non ne esce un numero razionale. */
static int value_now(Rat chosen, Frac *value) {
    Num number;
    if (!substituted(chosen, &chosen) || !rat_number(chosen, &number) || number.im.num != 0) return 0;
    *value = number.re;
    return 1;
}

/* Quanti elementi di ogni insieme prova la verifica: SAMPLE_SIZE, oppure meno
 * quando i quantificatori annidati sono tanti. Lo fissa decide_quantified(). */
static int sample_width;

/* Mette in out i valori che la verifica prova per una variabile di set, e
 * ritorna quanti sono: i primi width elementi (numbers_sample()), più il
 * primo che non è intero se tra quelli non ce n'è nessuno e set non è fatto
 * di interi. out deve avere posto per width + 1 valori.
 *
 * Perché. In ordine di altezza i primi razionali sono 0, 1, -1, 2, -2: con
 * cinque o più variabili annidate la larghezza scende a cinque o meno, e la
 * verifica di un enunciato sui razionali provava soltanto interi. Una copia
 * del programma rotta apposta, che non chiedeva che il valore di un
 * "esiste" fosse intero, "dimostrava" così che per x, y, z, w razionali con
 * x - y e z - w interi anche xz - yw è intero, e la verifica confermava: la
 * tesi fallisce solo fuori dagli interi (x = 0, y = 1, z = w = 1/2).
 * L'enunciato è in false_rare_witnesses.tex. Il valore si aggiunge e non ne
 * sostituisce un altro, perché un "esiste" che si confermava con -2 deve
 * continuare a trovarlo. */
static int check_sample(const NumberSet *set, Frac *out, int width) {
    Frac first[SAMPLE_SIZE];
    numbers_sample(set, out, width);
    if (set->integers) return width;
    for (int i = 0; i < width; i++)
        if (out[i].den != 1) return width;
    numbers_sample(set, first, SAMPLE_SIZE);
    for (int i = width; i < SAMPLE_SIZE; i++)
        if (first[i].den != 1) { out[width] = first[i]; return width + 1; }
    return width;
}

/* Quante volte la verifica ha trovato vera la tesi di un'implicazione dopo
 * averne trovata vera l'ipotesi: le prove che hanno controllato qualcosa
 * (vedi "Quante prove servono", in testa al capitolo). */
static long sample_theses;

/* Ritorna holds, la tesi di un'implicazione calcolata sul campione con
 * l'ipotesi vera, e la conta se è vera. */
static int thesis_counted(int holds) {
    sample_theses += holds;
    return holds;
}

/* Una condizione da rendere vera da cui la verifica ricava dei valori da
 * provare (sample_candidates()): un'uguaglianza, con al più un numero
 * ancora da scegliere, il testimone, che varia in `set`.
 *
 *   - source è F_EQUAL o F_DISTINCT: left = right. witness è la lettera di
 *     un "esiste" più interno che vi compare, o 0 se non ce n'è.
 *   - source è F_DIVIDES, "u divide v": per definizione v = q u con q
 *     intero (17n); il testimone è q, set sono gli interi, witness è 0.
 *   - source è F_IN, "s appartiene ad A": s = q con q in A; set è A. */
typedef struct {
    const Formula *source;
    int witness;
    const NumberSet *set;  /* NULL se non c'è un testimone */
} Wanted;

/* Gli interi: l'insieme del quoziente di una divisibilità. */
static const NumberSet all_integers = {.integers = 1};

/* Un quantificatore gia visitato dal verificatore numerico: formula e il
 * nodo originale, outer il contesto esterno preso in prestito. Ogni cella
 * vive nel proprio frame ricorsivo; i risultati conservano solo Formula*. */
typedef struct SampleBinder SampleBinder;
struct SampleBinder { const Formula *formula; const SampleBinder *outer; };

/* Elenca in list[], dal posto count, le condizioni da rendere vere perché
 * valga f, negata se negated, e ritorna il nuovo numero, al più
 * MAX_EQUATIONS. outer collega gli "esiste" esterni gia incontrati:
 * le loro lettere sono testimoni, senza limite sulla profondita della pila.
 *
 * Fa per la verifica ciò che find_equations() fa per la dimostrazione, ed è
 * scritta a parte perché chi controlla non usi il codice di chi cerca. In una
 * congiunzione prende ciò che serve, in una disgiunzione ciò che basta: in
 * tutti e due i casi è solo un valore da provare, e il conto lo ricontrolla.
 * Non entra in un "per ogni" più interno, dove un'uguaglianza vale per ogni
 * valore della sua lettera e risolverla non dà nulla. Entra in un "esiste",
 * e ne tiene anche le uguaglianze con la sua lettera: sono le ipotesi
 * "esiste k" di 18u, che si soddisfano scegliendo k. Un'uguaglianza con due
 * testimoni si salta, e così una divisibilità o un'appartenenza che ne usa
 * già uno: i valori da scegliere sarebbero due. */
static int sample_equations(const Formula *f, int negated, const SampleBinder *outer, Wanted *list, int count) {
    if (count == MAX_EQUATIONS) return count;
    switch (f->kind) {
    case F_NOT:
        return sample_equations(f->a, !negated, outer, list, count);
    case F_EQUAL: case F_DISTINCT: case F_DIVIDES: case F_IN: {
        /* I testimoni che vi compaiono, e da che parte va letta. */
        const Formula *binder = NULL;
        int witnesses = 0, plain = f->kind == F_EQUAL || f->kind == F_DISTINCT;
        for (const SampleBinder *p = outer; p; p = p->outer)
            if (formula_uses_letter(f, p->formula->variable)) { binder = p->formula; witnesses++; }
        if (plain ? (f->kind == F_EQUAL) == negated || witnesses > 1 : f->swapped != negated || witnesses) return count;
        if (plain) list[count] = binder ? (Wanted){f, binder->variable, &binder->numbers} : (Wanted){f, 0, NULL};
        else list[count] = (Wanted){f, 0, f->kind == F_IN ? &f->numbers : &all_integers};
        return count + 1;
    }
    case F_FORALL: case F_EXISTS: {
        if ((f->kind == F_EXISTS) == negated) return count;
        SampleBinder inner = {f, outer};
        return sample_equations(f->a, negated, &inner, list, count);
    }
    case F_AND: case F_OR:
        count = sample_equations(f->a, negated, outer, list, count);
        return sample_equations(f->b, negated, outer, list, count);
    case F_IMPLIES:
        count = sample_equations(f->a, !negated, outer, list, count);
        return sample_equations(f->b, negated, outer, list, count);
    default:
        return count;
    }
}

/* Fin dove la verifica prova gli interi, in valore assoluto, per una lettera
 * che compare solo negli esponenti (sample_exponent()). */
#define EXPONENT_SCAN 40

/* 18x, per la verifica. Il valore intero della variabile name che rende vera
 * l'uguaglianza w quando il suo testimone vale q, se name vi compare solo
 * negli esponenti: a = 2^{m} c non è di primo grado in m, ma con a e c
 * numeri il valore di m, se c'è, si trova provando gli interi da 0 verso
 * l'esterno, fino a EXPONENT_SCAN. Lo mette in *value e ritorna 1 se lo
 * trova. È un conto con i numeri, come il resto della verifica: senza, la
 * verifica di "a = 2^{n} b e b = 2^{k} c implicano a = 2^{m} c" provava per
 * m solo i primi interi, e non trovava m = -7 per a = 1, c = 128. */
static int sample_exponent(int name, const Wanted *w, Frac q, Frac *value) {
    const Formula *f = w->source;
    if (!formula_uses_letter(f, name)) return 0;
    for (int i = 0; i <= 2 * EXPONENT_SCAN; i++) {
        long long m = i % 2 ? (i + 1) / 2 : -(i / 2);
        size_t mark = arena_used;
        Num gap;
        if (w->witness) env_push(w->witness, rat_frac(q));
        env_push(name, rat_int(m));
        int zero = rat_number(rat_add(eval(f->left), eval(f->right), 1), &gap) && num_is_zero(gap) && !failure;
        env_pop();
        if (w->witness) env_pop();
        failure = NULL;
        arena_used = mark;
        if (zero) { *value = frac_int(m); return 1; }
    }
    return 0;
}

/* Il numeratore e il denominatore della condizione w, scritta come
 * polinomio uguale a zero, quando il suo testimone vale q. */
static Rat sample_gap(const Wanted *w, Frac q) {
    const Formula *f = w->source;
    if (f->kind == F_DIVIDES) return rat_add(eval(f->right), rat_mul(rat_frac(q), eval(f->left)), 1);
    if (f->kind == F_IN) return rat_add(eval(f->left), rat_frac(q), 1);
    if (w->witness) env_push(w->witness, rat_frac(q));
    Rat gap = rat_add(eval(f->left), eval(f->right), 1);
    if (w->witness) env_pop();
    return gap;
}

/* Il valore della variabile name che rende vera la condizione w quando il
 * suo testimone vale q, con tutte le altre variabili legate a numeri. Lo
 * mette in *value e ritorna 1 se la condizione, scritta come polinomio
 * uguale a zero, è di primo grado in name con coefficienti numerici, e se in
 * quel valore il denominatore non si annulla; oppure, se name compare solo
 * negli esponenti, se sample_exponent() lo trova. Un conto che non riesce
 * vuol dire solo che da qui non viene un valore.
 *
 * Se la condizione contiene un'applicazione definita per casi il cui
 * argomento dipende da name (11v), in *pieces va il numero dei suoi casi, e
 * si usa il caso piece: il valore del caso nell'equazione, oppure il punto
 * stesso, se il caso è "x = c". Con piece fuori dai casi non c'è un valore.
 * È solo un valore da provare: chi chiama lo ricontrolla calcolando con i
 * numeri, dove il caso si decide da sé. */
static int sample_solution(int name, const Wanted *w, Frac q, int piece, int *pieces, Frac *value) {
    const Formula *f = w->source;
    size_t mark = arena_used;
    Poly num, den, part[2];
    Num zero;
    int x = atom_var(name), forced = 0;
    *pieces = 0;
    Rat gap = sample_gap(w, q);
    if (failure == CASE_UNDECIDED && poly_uses(undecided_argument.num, x)) {
        const Map *map = undecided_map;
        Rat argument = undecided_argument;
        failure = NULL;
        *pieces = map->cases;
        if (piece < 0 || piece >= map->cases || case_choice_count == MAX_CASE_CHOICES) { arena_used = mark; return 0; }
        if (rat_same(argument, rat_atom(x)) && case_point(map, piece, value)) { arena_used = mark; return 1; }
        case_choice[case_choice_count++] = (CaseChoice){undecided_node, argument, piece};
        forced = 1;
        gap = sample_gap(w, q);
    }
    int solved = !failure && rat_polynomials(gap, &num, &den) && poly_split(num, x, part, 1) == 1 &&
                 poly_is_constant(part[0]) && poly_is_constant(part[1]) && part[1].term[0].coef.im.num == 0 &&
                 (part[0].count == 0 || part[0].term[0].coef.im.num == 0);
    if (solved) *value = frac_neg(frac_div(part[0].count ? part[0].term[0].coef.re : frac_int(0), part[1].term[0].coef.re));
    solved = solved && !(rat_number(poly_substitute(den, x, rat_frac(*value)), &zero) && num_is_zero(zero)) && !failure;
    if (forced) case_choice_count--;
    failure = NULL;
    arena_used = mark;
    if (!solved && (f->kind == F_EQUAL || f->kind == F_DISTINCT) && letter_only_in_exponents(f, name))
        solved = sample_exponent(name, w, q, value);
    return solved;
}

/* Mette in value[] i valori di name, al più SAMPLE_SIZE, che rendono vera
 * una delle condizioni list[0..wanted) e che stanno in set, escludendo quelli
 * già in known[0..knowns); ritorna quanti sono. Prima le condizioni senza
 * testimone, che danno un valore ciascuna; poi quelle con un testimone, che
 * prende i valori di check_sample() con larghezza width.
 *
 * Tra quei valori c'è anche quello che la verifica proverà per un "esiste"
 * k scritto nell'enunciato (sample_holds() prova gli stessi), quindi
 * l'ipotesi "esiste k con x = k^2" risulta vera per ogni x così ottenuto. */
static int sample_candidates(int name, const NumberSet *set, const Wanted *list, int wanted, int width, const Frac *known,
                             int knowns, Frac *value) {
    int count = 0;
    for (int witnessed = 0; witnessed < 2; witnessed++) {
        for (int e = 0; e < wanted && count < SAMPLE_SIZE; e++) {
            Frac q[SAMPLE_SIZE + 1];
            if ((list[e].set != NULL) != witnessed) continue;
            int tries = witnessed ? check_sample(list[e].set, q, width) : 1;
            for (int t = 0; t < tries && count < SAMPLE_SIZE; t++) {
                /* Con un'applicazione definita per casi, un valore per
                 * ogni caso (sample_solution()). */
                for (int piece = -1, pieces = 0; piece < pieces && count < SAMPLE_SIZE; piece++) {
                    Frac x;
                    if (!sample_solution(name, &list[e], witnessed ? q[t] : frac_int(0), piece, &pieces, &x) || !numbers_contain(set, x)) continue;
                    int seen = 0;
                    for (int i = 0; i < knowns && !seen; i++) seen = frac_cmp(known[i], x) == 0;
                    for (int i = 0; i < count && !seen; i++) seen = frac_cmp(value[i], x) == 0;
                    if (!seen) value[count++] = x;
                }
            }
        }
    }
    return count;
}

/* Il campione puo avere molti quantificatori: la larghezza suggerita
 * limita le combinazioni usuali, ma due valori per 40 lettere sono gia
 * oltre un trilione. Ogni visita reale ha quindi un budget separato,
 * configurabile; esaurirlo e mancata verifica, mai conferma parziale. */
static unsigned long long verification_left;
static int verification_limited;
static const char verification_problem[] = "budget di lavoro della verifica indipendente esaurito";

/* Conta una visita del verificatore numerico, senza traboccare il contatore. */
static int verification_step(void) {
    if (verification_limited || !verification_left) {
        verification_limited = 1; fail(verification_problem); return 0;
    }
    verification_left--;
    return 1;
}

/* Prototipo in avanti inevitabile: sample_holds() e sample_at() si chiamano
 * a vicenda. */
static int sample_holds(const Formula *f, int negated);

/* Calcola sul campione la condizione del quantificatore f, negata se
 * negated, con la sua variabile uguale a value; ritorna 1 se risulta vera.
 * Se il "per ogni" f è stato dimostrato per casi sul resto (18o), il numero
 * dice in quale caso si è, e quanto vale il quoziente che la dimostrazione
 * ha usato. */
static int sample_at(const Formula *f, int negated, Frac value) {
    int every = (f->kind == F_FORALL) != negated;
    int cases = every && f->modulus && value.den == 1, outer = split_case;
    env_push(f->variable, rat_frac(value));
    if (cases) {
        long long r = ((value.num % f->modulus) + f->modulus) % f->modulus;
        env_push(f->quotient, rat_int((value.num - r) / f->modulus));
        split_case = (int)r;
    }
    int holds = sample_holds(f->a, negated);
    if (cases) env_pop();
    split_case = outer;
    env_pop();
    return holds;
}

/* Ritorna 1 se la condizione f, negata se negated, risulta vera calcolando
 * con i numeri sul campione, come descritto in testa al capitolo. Tutte le
 * variabili visibili in f devono essere legate a numeri.
 *
 * I conti non lasciano nulla che serva dopo, solo un sì o un no: ogni volta
 * la memoria usata viene restituita all'arena riportando arena_used dov'era.
 * Senza questo passo, le migliaia di confronti di un enunciato con molte
 * variabili riempivano l'arena, e un enunciato vero restava non confermato. */
static int sample_holds(const Formula *f, int negated) {
    if (!verification_step()) return 0;
    Frac sample[SAMPLE_SIZE + 1], value;
    Num left, right;
    size_t mark = arena_used;
    if (failure) return 0;

    switch (f->kind) {
    case F_NOT:
        return sample_holds(f->a, !negated);
    case F_MAP:
        return !negated;
    case F_IN: {
        /* Il valore è un numero: basta guardare se sta nell'insieme. */
        int numbers = rat_number(eval(f->left), &left) && left.im.num == 0;
        arena_used = mark;
        return numbers && (numbers_contain(&f->numbers, left.re) != f->swapped) != negated;
    }
    case F_DIVIDES: {
        /* Due numeri: basta dividere. */
        int numbers = rat_number(eval(f->left), &left) && rat_number(eval(f->right), &right);
        arena_used = mark;
        return numbers && (number_divides(left, right) != f->swapped) != negated;
    }
    case F_LESS: case F_LESS_EQ: case F_SOLVE:
        /* Gli enunciati con una relazione d'ordine e gli insiemi di
         * soluzioni li decide e li ricontrolla la tabella dei segni (18p):
         * qui non arrivano. */
        return 0;
    case F_EQUAL: case F_DISTINCT: {
        /* Espressioni non razionali: come nella dimostrazione, il confronto
         * conta solo se i due membri esistono (closed_gap()). Gli atomi nati
         * dal conto, come la radice di 2, vanno tolti insieme alla memoria:
         * le loro basi vi abitano. */
        if (!term_is_rational(f->left) || !term_is_rational(f->right)) {
            Scratch before = scratch_mark();
            int equal = closed_gap(f);
            scratch_drop(before);
            return equal >= 0 && (equal == (f->kind == F_EQUAL)) != negated;
        }
        int numbers = rat_number(eval(f->left), &left) && rat_number(eval(f->right), &right);
        arena_used = mark;
        return numbers && (num_equal(left, right) == (f->kind == F_EQUAL)) != negated;
    }
    case F_AND:
        return negated ? sample_holds(f->a, 1) || sample_holds(f->b, 1) : sample_holds(f->a, 0) && sample_holds(f->b, 0);
    case F_OR:
        return negated ? sample_holds(f->a, 1) && sample_holds(f->b, 1) : sample_holds(f->a, 0) || sample_holds(f->b, 0);
    case F_IMPLIES:
        return negated ? sample_holds(f->a, 0) && sample_holds(f->b, 1) : sample_holds(f->a, 1) || thesis_counted(sample_holds(f->b, 0));
    case F_IFF: {
        /* Le due implicazioni, come in establish(). */
        if (negated) return (sample_holds(f->a, 0) && sample_holds(f->b, 1)) || (sample_holds(f->b, 0) && sample_holds(f->a, 1));
        int forward = sample_holds(f->a, 1) || thesis_counted(sample_holds(f->b, 0));
        return forward && (sample_holds(f->b, 1) || thesis_counted(sample_holds(f->a, 0)));
    }
    case F_FORALL: case F_EXISTS:
        break;
    }

    /* "Esiste": il valore scelto dalla dimostrazione, e solo quello. Deve
     * essere un numero dell'insieme e soddisfare la condizione.
     *
     * Se non regge non se ne cerca un altro: la dimostrazione ha affermato
     * qualcosa di quel valore, ed è quello che va controllato. Prima la
     * verifica ripiegava sugli elementi del campione, e una dimostrazione
     * sbagliata ("nessun x dà y = -2") veniva confermata trovando un altro y
     * la cui controimmagine era semplicemente fuori dal campione. */
    int every = (f->kind == F_FORALL) != negated;
    if (!every && (f->has_witness >> split_case & 1)) {
        int holds = value_now(f->witness[split_case], &value) && numbers_contain(&f->numbers, value);
        arena_used = mark;
        if (holds) {
            env_push(f->variable, rat_frac(value));
            holds = sample_holds(f->a, negated);
            env_pop();
            arena_used = mark;
        }
        return holds;
    }

    /* "Per ogni": tutti gli elementi del campione. "Esiste" per cui la
     * dimostrazione non ha scelto un valore, perché non le è servito: almeno
     * uno. */
    int samples = check_sample(&f->numbers, sample, sample_width);
    for (int i = 0; i < samples; i++) {
        int holds = sample_at(f, negated, sample[i]);
        arena_used = mark;
        if (holds != every) return holds;
    }

    /* Oltre ai primi elementi dell'insieme, i valori che le condizioni
     * impongono (vedi "I valori da provare", in testa al capitolo): per
     * smentire un "per ogni", o confermare un "esiste", serve un valore che
     * renda vera una condizione. Senza questo passo l'ipotesi \exists k \in
     * \mathbb{Z}\ (a - b = 7k) risultava falsa per a = 50 e b = 1, perché k
     * = 7 non è tra i primi interi; e x = k^2 + 7 non era vera per nessuno
     * dei primi x. Un'implicazione con l'ipotesi falsa conferma qualsiasi
     * dimostrazione. */
    Wanted wanted[MAX_EQUATIONS];
    Frac candidate[SAMPLE_SIZE];
    int conditions = sample_equations(f->a, every ? !negated : negated, NULL, wanted, 0);
    int candidates = sample_candidates(f->variable, &f->numbers, wanted, conditions, sample_width, sample, samples, candidate);
    for (int i = 0; i < candidates; i++) {
        int holds = sample_at(f, negated, candidate[i]);
        arena_used = mark;
        if (holds != every) return holds;
    }
    return every;
}

/* Dimentica ciò che una dimostrazione ha annotato nei nodi di f: i valori
 * scelti e i casi sul resto. Va chiamata prima di riusare la memoria in cui
 * quei valori stanno. */
static void forget_choices(Formula *f) {
    if (!f) return;
    f->has_witness = 0;
    f->modulus = 0;
    forget_choices(f->a);
    forget_choices(f->b);
}

/* Quanti valori provare per ogni variabile quando le variabili da combinare
 * sono depth: le combinazioni sono larghezza^depth, e si scende da
 * SAMPLE_SIZE finché non stanno in MAX_CHECKS. Mai meno di due valori. */
static int width_for(int depth) {
    int width = SAMPLE_SIZE;
    for (;;) {
        long long combinations = 1;
        for (int i = 0; i < depth && combinations <= MAX_CHECKS; i++) {
            if (combinations > MAX_CHECKS / width) { combinations = MAX_CHECKS + 1; break; }
            combinations *= width;
        }
        if (combinations <= MAX_CHECKS || width == 2) return width;
        width--;
    }
}

/* Lega, sopra le variabili generiche già legate a numeri, le variabili che
 * nella dimostrazione annotata in r avevano un valore, con quel valore
 * calcolato in quei numeri: un numero, o un'espressione nelle generiche non
 * ancora legate. Ritorna quante ne ha legate, o -1, senza legarne nessuna,
 * se un conto non riesce o se env non ha abbastanza posti. */
static int bindings_push(const WitnessRecord *r) {
    int saved = env_count;
    for (int i = 0; i < r->bindings; i++) {
        Rat value;
        if (!substituted(r->binding[i].value, &value)) {
            while (i-- > 0) env_pop();
            return -1;
        }
        if (!env_push(r->binding[i].name, value)) { env_count = saved; return -1; }
    }
    return r->bindings;
}

/* Ritorna 1 se ciò che r afferma regge quando le prime `level` variabili
 * generiche di r sono legate a numeri e le altre li prendono come descritto
 * in testa al capitolo: ognuna i valori che le ipotesi le impongono, se ce
 * ne sono, altrimenti i valori di check_sample() con larghezza width.
 * Aggiunge a *satisfied le scelte in cui le ipotesi valgono.
 *
 * Un'ipotesi che in quei numeri non è definita (una divisione per zero) lì
 * non vale, e la scelta non conta. Ogni altro conto che non riesce, nelle
 * ipotesi, nei valori scelti o nella condizione, vuol dire che ciò che r
 * afferma non è confermato. */
static int record_holds(const WitnessRecord *r, int level, int width, long *satisfied) {
    if (!verification_step()) return 0;
    size_t mark = arena_used;
    if (failure) return 0;
    int pushed = bindings_push(r);
    if (pushed < 0) return 0;

    /* Tutte le generiche hanno un numero: prima le ipotesi, poi i valori
     * scelti, il loro insieme e la condizione. */
    if (level == r->generics) {
        int met = 1, holds = 1, named = 0;
        for (int i = 0; i < r->leaves && met && !failure; i++) {
            undefined = 0;
            met = sample_holds(r->leaf[i].source, !r->leaf[i].negated);
            if (failure && undefined) failure = NULL;
        }
        if (met) {
            (*satisfied)++;
            for (int j = 0; j < r->names && holds; j++) {
                Frac w;
                holds = value_now(r->value[j], &w) && numbers_contain(&r->quantifier[j]->numbers, w);
                if (holds) { env_push(r->quantifier[j]->variable, rat_frac(w)); named++; }
            }
            holds = holds && sample_holds(r->body, r->sign);
        }
        while (named-- > 0) env_pop();
        while (pushed-- > 0) env_pop();
        arena_used = mark;
        return holds && !failure;
    }

    /* La variabile di questo livello: i valori che le ipotesi le impongono,
     * calcolati con le variabili già legate, o quelli di check_sample(). */
    const Bound *g = &r->generic[level];
    Wanted wanted[MAX_EQUATIONS];
    Frac value[SAMPLE_SIZE + 1];
    int conditions = 0;
    for (int i = 0; i < r->leaves; i++)
        conditions = sample_equations(r->leaf[i].source, !r->leaf[i].negated, NULL, wanted, conditions);
    int values = sample_candidates(g->name, g->numbers, wanted, conditions, width, NULL, 0, value);
    while (pushed-- > 0) env_pop();
    arena_used = mark;
    if (!values) values = check_sample(g->numbers, value, width);
    for (int i = 0; i < values; i++) {
        env_push(g->name, rat_frac(value[i]));
        int holds = record_holds(r, level + 1, width, satisfied);
        env_pop();
        arena_used = mark;
        if (!holds) return 0;
    }
    return 1;
}

/* La verifica dei valori annotati da 18u-3 (record_holds()). Ritorna NULL se
 * reggono tutti, ognuno su abbastanza scelte che soddisfano le ipotesi (vedi
 * "Quante prove servono", in testa al capitolo); altrimenti il motivo per cui
 * il verdetto non va emesso. */
static const char *records_doubt(void) {
    for (int k = 0; k < record_count; k++) {
        const WitnessRecord *r = &witness_records[k];
        long satisfied = 0;
        verification_left = verification_work_limit; verification_limited = 0;
        int holds = record_holds(r, 0, width_for(r->generics), &satisfied);
        failure = NULL;
        if (verification_limited) return verification_problem;
        if (!holds) return "la verifica indipendente, sui numeri, non conferma un valore scelto dalla dimostrazione per un \"esiste\"";
        if (satisfied < MIN_SATISFIED)
            return "la verifica indipendente non ha trovato valori che soddisfano le ipotesi con cui ricontrollare un valore scelto dalla dimostrazione";
    }
    return NULL;
}

/* Calcola con i numeri l'immagine dell'elemento value del dominio di map,
 * un'applicazione definita per casi (17s), senza fidarsi del primo caso che
 * vale: tutti i casi che valgono devono dare lo stesso numero, e almeno uno
 * deve valere. Se la regola com'è scritta c'è (i casi vengono dai suoi
 * valori assoluti), anche lei deve dare quel numero: è il controllo della
 * lettura per casi. Mette il numero in *image e ritorna 1 se tutto torna. */
static int cases_image(const Map *map, Rat value, Num *image) {
    int found = 0;
    Num other;
    env_push(map->parameter, value);
    for (int i = 0; i < map->cases && !failure; i++) {
        int holds = condition_computed(map->piece[i].when);
        if (holds < 0) found = -1;
        if (holds != 1 || found < 0) continue;
        if (!rat_number(eval(map->piece[i].value), &other)) found = -1;
        else if (found && !num_equal(other, *image)) found = -1;
        else { *image = other; found = 1; }
    }
    if (found > 0 && map->body && (!rat_number(eval(map->body), &other) || !num_equal(other, *image))) found = -1;
    env_pop();
    return found > 0 && !failure;
}

/* Ritorna 1 se, sul campione del dominio, la regola di map dà sempre un
 * numero che sta nel codominio. Per una definizione per casi, lo dà nel
 * modo di cases_image(). */
static int map_holds_on_sample(const Map *map) {
    Frac sample[SAMPLE_SIZE], other[SAMPLE_SIZE];
    numbers_sample(&map->domain, sample, SAMPLE_SIZE);

    /* Per un'operazione, ogni coppia del campione dei due insiemi. */
    int seconds = map->binary ? SAMPLE_SIZE : 1;
    if (map->binary) numbers_sample(&map->second, other, SAMPLE_SIZE);
    for (int i = 0; i < SAMPLE_SIZE; i++) {
        for (int j = 0; j < seconds; j++) {
            Num value;
            if (map->cases) {
                if (!cases_image(map, rat_frac(sample[i]), &value)) return 0;
            } else {
                env_push(map->parameter, rat_frac(sample[i]));
                if (map->binary) env_push(map->parameter2, rat_frac(other[j]));
                Rat image = eval(map->body);
                if (map->binary) env_pop();
                env_pop();
                if (failure || !rat_number(image, &value)) return 0;
            }
            if (value.im.num != 0 || !numbers_contain(&map->codomain, value.re)) return 0;
        }
    }
    return 1;
}

/* Ritorna, per un'applicazione definita per casi i cui casi non si sono
 * dimostrati una definizione (18v-6), che cosa trova il campione del
 * dominio: un punto in cui nessun caso vale, due casi che valgono insieme e
 * danno valori diversi, o un valore fuori dal codominio. Il motivo sta in un
 * testo che vale fino alla chiamata successiva; NULL se il campione non trova
 * nulla, o se le condizioni non si calcolano con i numeri, perché nominano
 * un parametro (17s). */
static const char *cases_fault(const Map *map) {
    static char reason[160];
    Frac sample[2 * SAMPLE_SIZE];
    Num value, other;
    numbers_sample(&map->domain, sample, 2 * SAMPLE_SIZE);
    for (int i = 0; i < 2 * SAMPLE_SIZE && !failure; i++) {
        int applies = 0, clash = 0;
        env_push(map->parameter, rat_frac(sample[i]));
        for (int k = 0; k < map->cases && !failure; k++) {
            int holds = condition_computed(map->piece[k].when);
            if (holds < 0) { env_pop(); failure = NULL; return NULL; }
            if (!holds || !rat_number(eval(map->piece[k].value), &other)) continue;
            if (applies++ && !num_equal(other, value)) clash = 1;
            value = other;
        }
        env_pop();
        if (failure) break;
        const char *what = !applies ? "nessun caso della definizione vale" : clash ? "due casi della definizione valgono e danno valori diversi"
                         : value.im.num || !numbers_contain(&map->codomain, value.re) ? "il valore cade fuori dal codominio" : NULL;
        if (!what) continue;
        int n = snprintf(reason, sizeof reason, "la definizione per casi non definisce un'applicazione: in %c = ", map->parameter);
        if (sample[i].den == 1) snprintf(reason + n, sizeof reason - (size_t)n, "%lld %s", sample[i].num, what);
        else snprintf(reason + n, sizeof reason - (size_t)n, "%lld/%lld %s", sample[i].num, sample[i].den, what);
        return reason;
    }
    failure = NULL;
    return NULL;
}

/* La verifica dell'enunciato e delle sue applicazioni, con i parametri
 * (17s) dal posto level in su legati, uno per volta, ai valori di
 * check_sample(): ciò che la dimostrazione ha stabilito per ogni valore dei
 * parametri deve reggere in ognuno. Con thesis NULL si guardano solo le
 * applicazioni. Ritorna 1 se tutto regge. */
static int sample_with_parameters(const Formula *thesis, int negated, int level) {
    if (level < statement_parameter_count && env_lookup(statement_parameters[level].name))
        return sample_with_parameters(thesis, negated, level + 1);
    if (level == statement_parameter_count) {
        int holds = !thesis || sample_holds(thesis, negated);
        for (int i = 0; i < map_count; i++) holds = holds && map_holds_on_sample(&maps[i]);
        return holds;
    }
    Frac value[SAMPLE_SIZE + 1];
    int values = check_sample(statement_parameters[level].numbers, value, sample_width);
    for (int i = 0; i < values; i++) {
        env_push(statement_parameters[level].name, rat_frac(value[i]));
        int holds = sample_with_parameters(thesis, negated, level + 1);
        env_pop();
        if (!holds) return 0;
    }
    return 1;
}

/* Il testo delle scelte fatte, per esempio "a = 0, b = 3". */
static char *choice_text;
static size_t choice_capacity;

/* Scrive in choice_text i numeri scelti dalla dimostrazione e ne ritorna
 * l'indirizzo, oppure NULL se non ce ne sono. */
static const char *describe_choices(void) {
    size_t length = 0;
    if (!chosen_count || chosen_by_cases) return NULL;
    /* 128 byte per numero bastano a segni, due interi a 64 bit e notazione
     * di coppie/complessi. Il numero dei legami decide la memoria, non un
     * testo fisso che potrebbe omettere parte del controesempio. */
    if ((size_t)chosen_count > ((size_t)-1 - 1) / 128 ||
        !work_reserve((void **)&choice_text, &choice_capacity, (size_t)chosen_count * 128 + 1, 1)) return NULL;
    for (int i = 0; i < chosen_count; i++) {
        /* 17t-2. Le due componenti di una coppia, scelte una dopo l'altra, si
         * scrivono come la coppia: x = (0, 1), o x = 0 + 1i per un numero
         * complesso (17t-4). */
        int pair = 0, complex = 0;
        for (int k = 0; k < pairs_seen_count && !pair && i + 1 < chosen_count; k++)
            if (pairs_seen[k].part[0] == chosen[i].name && pairs_seen[k].part[1] == chosen[i + 1].name) {
                pair = pairs_seen[k].letter;
                complex = pairs_seen[k].complex;
            }
        if (length < choice_capacity && pair)
            length += (size_t)snprintf(choice_text + length, choice_capacity - length, complex ? "%s%c = " : "%s%c = (", i ? ", " : "", pair);
        for (int j = i; j <= i + (pair != 0); j++) {
            Frac v = chosen[j].value;
            const char *between = j == i ? "" : complex ? (v.num < 0 ? " - " : " + ") : ", ";
            if (complex && j > i && v.num < 0) v.num = -v.num;
            if (length < choice_capacity && !pair)
                length += (size_t)snprintf(choice_text + length, choice_capacity - length, "%s%c = ", i ? ", " : "", chosen[j].name);
            if (length < choice_capacity)
                length += (size_t)snprintf(choice_text + length, choice_capacity - length, "%s%lld", between, v.num);
            if (v.den != 1 && length < choice_capacity)
                length += (size_t)snprintf(choice_text + length, choice_capacity - length, "/%lld", v.den);
        }
        if (length < choice_capacity && pair) length += (size_t)snprintf(choice_text + length, choice_capacity - length, complex ? "i" : ")");
        if (pair) i++;
    }
    return choice_text;
}

/* Verifica indipendente della regola 18r, e il suo verdetto.
 *
 * La regola calcola con i resti: polinomi ridotti modulo un numero, sulle
 * condizioni che ha messo in tabella. Qui lo stesso enunciato viene
 * ricalcolato com'è scritto, senza tabella e senza resti: ogni variabile
 * prende per valore gli interi veri di un periodo, residue_period elementi
 * consecutivi del suo insieme (non i numeri da 0 a M - 1 usati dalla regola,
 * ma quelli da cui l'insieme comincia, o a cavallo dello zero), e ogni
 * condizione è una divisione tra due numeri esatti del capitolo 11. Per il
 * teorema in testa a 18r anche questo è un conto completo: se i due non
 * danno la stessa risposta uno dei due è sbagliato, e il verdetto non viene
 * emesso. */

/* Ritorna il k-esimo, per k da 0 a residue_period - 1, di una fila di
 * elementi di set con resti tutti diversi modulo residue_period: interi
 * consecutivi, e al posto di uno che manca da set il primo dopo di lui con lo
 * stesso resto. */
static long long period_member(const NumberSet *set, long long k) {
    long long x = (set->bounded ? set->low + set->strict : -(residue_period / 2)) + k;
    while (!numbers_contain(set, frac_int(x))) x += residue_period;
    return x;
}

/* Ritorna 1 se esiste un intero k, la variabile di nome name, che soddisfa
 * una delle uguaglianze di e; ogni altra variabile ha un numero per valore.
 * Un'uguaglianza di primo grado in k ha una sola soluzione, e si guarda se è
 * intera; una in cui k non compare vale o non vale per ogni k. */
static int multiple_exists(const Formula *e, int name) {
    Poly num, den, part[2];
    Num slope = num_int(0), constant;
    size_t mark = arena_used;
    if (e->kind == F_OR) return multiple_exists(e->a, name) || multiple_exists(e->b, name);
    Rat gap = rat_add(eval(e->left), eval(e->right), 1);
    int degree = !failure && rat_polynomials(gap, &num, &den) ? poly_split(num, atom_var(name), part, 1) : -1;
    Poly one = poly_const(num_int(1));
    int numbers = degree >= 0 && rat_number((Rat){part[0], one}, &constant) && (degree == 0 || rat_number((Rat){part[1], one}, &slope));
    arena_used = mark;
    if (!numbers) { fail("la verifica sugli interi non sa leggere un'uguaglianza"); return 0; }
    return degree == 0 ? num_is_zero(constant) : number_divides(slope, constant);
}

/* Ritorna 1 se la condizione f, del linguaggio di 18r, è vera calcolando con
 * gli interi: ogni variabile visibile in f deve essere legata a un numero.
 * Un quantificatore prova gli interi di un periodo del suo insieme. Se un
 * conto non riesce annota l'errore: chi chiama non deve fidarsi della
 * risposta. */
static int period_holds(const Formula *f) {
    Num left, right;
    size_t mark = arena_used;
    if (failure) return 0;
    switch (f->kind) {
    case F_NOT:     return !period_holds(f->a);
    case F_AND:     return period_holds(f->a) && period_holds(f->b);
    case F_OR:      return period_holds(f->a) || period_holds(f->b);
    case F_IMPLIES: return !period_holds(f->a) || period_holds(f->b);
    case F_IFF:     return period_holds(f->a) == period_holds(f->b);
    case F_DIVIDES: {
        int numbers = rat_number(eval(f->left), &left) && rat_number(eval(f->right), &right);
        arena_used = mark;
        if (!numbers) fail("la verifica sugli interi non sa calcolare una condizione");
        return numbers && number_divides(left, right) != f->swapped;
    }
    case F_IN: {
        int numbers = rat_number(eval(f->left), &left) && left.im.num == 0;
        arena_used = mark;
        if (!numbers) fail("la verifica sugli interi non sa calcolare una condizione");
        return numbers && numbers_contain(&f->numbers, left.re) != f->swapped;
    }
    case F_FORALL: case F_EXISTS:
        break;
    default:
        fail("la verifica sugli interi ha trovato una condizione che non conosce");
        return 0;
    }
    if (names_a_multiple(f)) return multiple_exists(f->a, f->variable);

    int every = f->kind == F_FORALL, holds = every;
    for (long long k = 0; k < residue_period && holds == every && !failure; k++) {
        env_push(f->variable, rat_int(period_member(&f->numbers, k)));
        holds = period_holds(f->a);
        env_pop();
    }
    return holds;
}

/* Cerca dei resti per le variabili dei "per ogni" in testa a f con cui ciò
 * che segue è falso. Se li trova ritorna 1 e li lascia in residue_name[] e
 * residue_value[], con residue_count variabili. */
static int residue_failure(const Formula *f) {
    if (f->kind != F_FORALL) return !residue_holds(f);
    residue_name[residue_count++] = f->variable;
    for (long long r = 0; r < residue_period; r++) {
        residue_value[residue_count - 1] = r;
        if (residue_failure(f->a)) return 1;
    }
    residue_count--;
    return 0;
}

/* Il testo di ciò che decide_by_residues() ha da riportare: un controesempio
 * come "x = 5, y = 0", oppure le soluzioni come condizione in LaTeX. */
static char residue_text[64 * MAX_CLASSES];

/* 18r, per \{x \in A \mid c\}: l'insieme delle soluzioni di una condizione c
 * del linguaggio di 18r, con A un insieme di interi. solve è il nodo F_SOLVE,
 * già accettato da congruences_read(); riempie *verdict.
 *
 * Le soluzioni sono gli x il cui resto modulo M è uno di quelli "buoni", che
 * si trovano provandoli tutti. Per scriverle come sui libri si cerca il
 * periodo più piccolo d che divide M: se i resti buoni si ripetono ogni d,
 * basta elencare quelli tra 0 e d - 1.
 *
 * Tre controlli, come per le soluzioni della tabella dei segni: i resti
 * buoni devono essere gli stessi calcolando con gli interi veri
 * (period_holds()); e le soluzioni scritte vengono rilette dal lettore del
 * programma e calcolate, sugli stessi interi, come una condizione qualsiasi. */
static void solve_by_residues(const Formula *solve, Verdict *verdict) {
    static char good[MAX_PERIOD];
    const NumberSet *set = &solve->numbers;
    long long period = residue_period, shortest = period, classes = 0;
    int name = solve->variable, length = 0, confirmed = 1;

    /* I resti buoni, con la regola; e la conferma sugli interi. */
    residue_name[0] = name;
    residue_count = 1;
    for (long long r = 0; r < period; r++) {
        residue_value[0] = r;
        good[r] = (char)residue_holds(solve->a);
    }
    residue_count = 0;
    for (long long k = 0; k < period && confirmed; k++) {
        long long x = period_member(set, k);
        env_push(name, rat_int(x));
        confirmed = period_holds(solve->a) == good[((x % period) + period) % period] && !failure;
        env_pop();
    }

    /* Il periodo più piccolo, e quanti resti buoni contiene. */
    for (long long d = 1; d < period && shortest == period; d++) {
        int repeats = period % d == 0;
        for (long long r = d; r < period && repeats; r++) repeats = good[r] == good[r - d];
        if (repeats) shortest = d;
    }
    for (long long r = 0; r < shortest; r++) classes += good[r];
    if (confirmed && classes > MAX_CLASSES && classes < shortest) {
        verdict->outcome = NOT_PROVED;
        verdict->reason = "le soluzioni sono troppe classi di resto per elencarle";
        return;
    }

    /* Le soluzioni scritte: nessuna, tutte, oppure le classi di resto. */
    int listed = classes > 0 && classes < shortest;
    if (!listed) length = snprintf(residue_text, sizeof residue_text, "%s %c \\in %.*s", classes ? "\\forall" : "\\nexists", name, (int)(set->end - set->start), set->start);
    for (long long r = 0; r < shortest && listed; r++)
        if (good[r]) length += snprintf(residue_text + length, sizeof residue_text - (size_t)length, "%s%c \\equiv %lld \\pmod{%lld}", length ? " \\lor " : "", name, r, shortest);

    /* Rilettura: ciò che è scritto, letto come una condizione, deve valere
     * esattamente dove vale la condizione di partenza. */
    if (listed && confirmed) {
        syntax_error = NULL;
        cursor = residue_text;
        next_token();
        const Formula *written = logic_formula();
        confirmed = !syntax_error && token.kind == T_END;
        for (long long k = 0; k < period && confirmed; k++) {
            long long x = period_member(set, k);
            env_push(name, rat_int(x));
            confirmed = period_holds(written) == good[((x % period) + period) % period] && !failure;
            env_pop();
        }
    }
    if (!confirmed) {
        failure = syntax_error = NULL;
        unjustified_steps++;
        verdict->outcome = NOT_PROVED;
        verdict->reason = "la verifica indipendente, sugli interi di un periodo, non conferma i resti trovati o le soluzioni scritte";
        return;
    }

    proof_add("Whether $%c$ satisfies the condition depends only on its remainder modulo $%lld$: each part of the condition says that "
              "a polynomial with integer coefficients is a multiple of a number that divides $%lld$. Trying the remainders "
              "$0, \\ldots, %lld$ one by one, the condition holds exactly for $%s$. $\\Box$", name, period, period, period - 1, residue_text);
    verdict->outcome = SOLVED;
    verdict->method = "provando tutti i resti";
    verdict->detail = residue_text;
    verdict->proof = proof_text;
}

/* 18r. Se l'enunciato thesis è fatto solo di congruenze tra interi lo decide
 * provando tutti i resti, riempie *verdict e ritorna 1; altrimenti ritorna 0
 * e non tocca nulla. Nessuna variabile deve essere legata, e la tabella degli
 * atomi deve essere quella dell'enunciato.
 *
 * Il verdetto è DIMOSTRATO o FALSO solo se il conto sui resti e quello sugli
 * interi di un periodo danno la stessa risposta; per un insieme di soluzioni
 * è RISOLTO (solve_by_residues()). */
static int decide_by_residues(const Formula *thesis, Verdict *verdict) {
    /* È del linguaggio? Un conto che non riesce vuol dire solo di no. */
    int deepest = 0;
    congruence_count = residue_count = 0;
    if (!congruences_read(thesis, &deepest) || failure) { failure = NULL; return 0; }

    /* Il periodo, e il numero di casi: devono restare trattabili. */
    long long cases = 1;
    residue_period = 1;
    for (int i = 0; i < congruence_count; i++) {
        __int128 multiple = (__int128)residue_period / gcd128(residue_period, congruences[i].modulus) * congruences[i].modulus;
        if (multiple > MAX_PERIOD) return 0;
        residue_period = (long long)multiple;
    }
    for (int i = 0; i < deepest; i++) {
        if (cases > MAX_RESIDUE_CASES / residue_period) return 0;
        cases *= residue_period;
    }
    proof_reset();
    if (thesis->kind == F_SOLVE) { solve_by_residues(thesis, verdict); return 1; }

    /* La regola, e la verifica indipendente. */
    int holds = residue_holds(thesis);
    int confirmed = period_holds(thesis) == holds && !failure;

    /* Un enunciato falso che comincia con dei "per ogni" ha un controesempio
     * da riportare: i resti trovati, portati dentro gli insiemi. Anche
     * questi numeri vengono ricontrollati, calcolando su di loro ciò che
     * segue i quantificatori. */
    const char *counterexample = NULL;
    if (confirmed && !holds && thesis->kind == F_FORALL && residue_failure(thesis)) {
        const Formula *body = thesis;
        int length = 0;
        for (int i = 0; i < residue_count; i++, body = body->a) {
            long long x = residue_value[i];
            while (!numbers_contain(&body->numbers, frac_int(x))) x += residue_period;
            env_push(body->variable, rat_int(x));
            length += snprintf(residue_text + length, sizeof residue_text - (size_t)length, "%s%c = %lld", i ? ", " : "", body->variable, x);
        }
        confirmed = !period_holds(body) && !failure;
        env_count = residue_count = 0;
        counterexample = residue_text;
    }
    if (!confirmed) {
        failure = NULL;
        unjustified_steps++;
        verdict->outcome = NOT_PROVED;
        verdict->reason = "la verifica indipendente, sugli interi di un periodo, non conferma il conto sui resti";
        return 1;
    }

    /* La dimostrazione scritta: le condizioni, il periodo, l'esito. */
    proof_add(holds ? "\\textbf{Proof.} " : "\\textbf{The statement is false.} ");
    proof_add("Written out, each condition of the statement says that a polynomial with integer coefficients is a multiple of a number: ");
    for (int i = 0; i < congruence_count; i++) {
        proof_add("%s$%lld$ divides $", i ? ", " : "", congruences[i].modulus);
        put_poly(congruences[i].dividend);
        proof_add("$");
    }
    proof_add(". Let $M = %lld$, a common multiple of these numbers. If a letter changes by a multiple of $M$, each polynomial "
              "changes by a multiple of $M$, so no condition changes; and each set of the statement contains integers with every "
              "remainder modulo $M$. It is therefore enough to give each letter the remainders $0, \\ldots, %lld$: %lld case%s. ",
              residue_period, residue_period - 1, cases, cases == 1 ? "" : "s");
    if (holds) proof_add("The statement holds in each of them. $\\Box$");
    else if (counterexample) proof_add("The statement fails for $%s$.", counterexample);
    else proof_add("Computing them shows that the statement is false.");
    verdict->outcome = holds ? PROVED : REFUTED;
    verdict->method = "provando tutti i resti";
    verdict->detail = counterexample;
    verdict->proof = proof_text;
    return 1;
}

/* Ritorna 1 se nella condizione f compare un nodo di tipo kind. */
static int formula_has_kind(const Formula *f, FormulaKind kind) {
    return f && (f->kind == kind || formula_has_kind(f->a, kind) || formula_has_kind(f->b, kind));
}

/* 18y. Ritorna 1 se nella condizione f compare una relazione d'ordine, o un
 * insieme di soluzioni: ciò che decide soltanto la tabella dei segni. */
static int formula_has_order(const Formula *f) {
    return formula_has_kind(f, F_LESS) || formula_has_kind(f, F_LESS_EQ) || formula_has_kind(f, F_SOLVE);
}

/* Prototipo in avanti inevitabile: le iterate di un'applicazione (17s) si
 * dimostrano come una successione definita per ricorrenza, con il metodo
 * del capitolo 26, che viene dopo (26c). */
static Verdict decide_iterates(const Formula *thesis);

/* Prototipi in avanti inevitabili: un enunciato con applicazioni tra reali si
 * decide svolgendo le definizioni (18v-8), e ciò che si ottiene è di nuovo un
 * enunciato con quantificatori, che decide questa stessa funzione. */
static int real_maps_unfoldable(void);
static Verdict decide_real_maps(const Formula *thesis);

/* Ritorna 1 se l'enunciato in corso definisce le iterate di
 * un'applicazione (17s). */
static int iterates_declared(void) {
    for (int i = 0; i < map_count; i++)
        if (maps[i].iterates) return 1;
    return 0;
}

/* Il lavoro di prove_quantified(), che ne descrive il contratto. Al ritorno
 * la tabella `maps` contiene ancora le applicazioni dell'enunciato. */
static Verdict decide_quantified(const char *formula) {
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, "con le regole sui quantificatori", NULL, NULL};

    /* Ripartenza da zero e parsing. */
    proof_reset();
    arena_used = arena_keep;

    /* Con la memoria ripartono anche le tabelle che vi puntano: gli atomi,
     * le basi che sono polinomi e gli argomenti delle arcotangenti. Le
     * ultime due una volta si azzeravano solo più avanti, dove comincia la
     * ricerca con le regole sui quantificatori: un enunciato deciso prima,
     * dalla tabella dei segni, lasciava ad atan_args[] un puntatore a
     * memoria già riusata, e l'enunciato successivo con un'arcotangente
     * leggeva dati a caso. */
    atom_count = base_poly_count = atan_count = 0;
    failure = NULL;
    env_count = 0;
    map_count = statement_parameter_count = 0;
    syntax_error = NULL;
    cursor = formula;
    next_token();
    Formula *thesis = logic_statement();
    if (token.kind != T_END) syntax("testo inatteso dopo l'enunciato");

    /* Come si sono lette le lettere di coppie (17t-2), per il verdetto:
     * subito, prima che una rilettura ne aggiunga altre. */
    pairs_note_write();

    /* 27j. I segni di derivata dentro le espressioni diventano derivate,
     * prima di ogni altro conto. */
    derivative_signs = 0;
    if (!syntax_error) formula_derivatives_expanded(thesis);

    /* Ipotesi e tesi, poi i controlli che la grammatica non fa. */
    if (!syntax_error && !failure) {
        if ((map_count > 0 || pair_set_count > 0) && thesis->kind == F_IMPLIES) {
            read_definitions(thesis->a);
            thesis = thesis->b;
        }
        for (int i = 0; i < map_count; i++)
            if (!maps[i].body && !maps[i].cases) fail("un'applicazione è dichiarata senza la regola che la definisce");
        pair_sets_check();

        /* I parametri (17s) sono visibili in tutta la tesi, salvo dove una
         * lettera legata li nasconde, e contano tra le variabili a cui la
         * verifica dà un valore. */
        unshadowed_note[0] = 0;
        if (statement_parameter_count && !failure) parameters_unshadowed(thesis);
        scope_parameters();
        quantifier_depth = statement_parameter_count;
        if (!failure) formula_check(thesis);
        scope_count = 0;
    }

    /* 26c. Le iterate di un'applicazione: una successione per ricorrenza. */
    if (!syntax_error && !failure && iterates_declared()) return decide_iterates(thesis);

    /* 27l. Un enunciato con segni di derivata lo decide solo la tabella dei
     * segni, in una variabile reale, e solo se le derivate espanse dicono
     * la derivata in ogni punto che conta. Le altre regole lavorano sui
     * razionali, dove una derivata non ha senso. */
    if (derivative_signs && !syntax_error && !failure) {
        const char *doubt = NULL;
        derivative_edges = 0;
        if (!formula_needs_signs(thesis) || map_count || pair_set_count || has_parameter(thesis) || formula_has_kind(thesis, F_IN) ||
            formula_has_kind(thesis, F_DIVIDES) || (thesis->kind == F_SOLVE && thesis->numbers.integers))
            verdict.reason = "il segno di derivata è trattato negli enunciati su una sola variabile reale, decisi dalla tabella dei segni";
        else if ((doubt = derivative_doubt(thesis))) {
            verdict.outcome = NOT_PROVED;
            verdict.reason = doubt;
        } else {
            decide_by_signs(thesis, &verdict);
            if (derivative_edges && !verdict.note) verdict.note = DERIVATIVE_EDGES;
        }
        return verdict;
    }

    /* 18r. Un insieme di soluzioni tra gli interi: la regola dei resti, se
     * la condizione è fatta di congruenze. */
    if (!syntax_error && !failure && thesis->kind == F_SOLVE && thesis->numbers.integers && !map_count && decide_by_residues(thesis, &verdict))
        return verdict;

    /* 18p. Relazioni d'ordine e numeri reali: li tratta solo la tabella dei
     * segni, che decide da sola. Le altre regole lavorano sui razionali e
     * con = e \neq. Con due lettere reali, un parametro e una variabile, la
     * tabella si fa per casi sul parametro (18t).
     *
     * 18y. Fa eccezione un enunciato sui numeri reali senza relazioni
     * d'ordine che parla di appartenenza o di divisibilità, come "a b^{-1}
     * \in \mathbb{Q}" tra reali positivi: la tabella dei segni non lo
     * tratta, e le regole del capitolo 18 sì, perché quelle che
     * presuppongono variabili razionali lo controllano (vedi 18y, in testa a
     * always_in()). */
    int real_membership = !map_count && !formula_has_order(thesis) &&
                          (formula_has_kind(thesis, F_IN) || formula_has_kind(thesis, F_DIVIDES));
    if (!syntax_error && !failure && formula_needs_signs(thesis) && !real_membership) {
        int reals = 0;
        for (int i = 0; i < map_count; i++) reals = reals || maps[i].domain.reals || maps[i].codomain.reals;
        if (reals && real_maps_unfoldable()) return decide_real_maps(thesis);
        if (reals)
            verdict.reason = "le applicazioni tra numeri reali si decidono svolgendo la definizione solo se regole e condizioni sono "
                             "polinomi, divisi al più per dei numeri, senza parametri né iterate, e con due argomenti solo se vengono "
                             "da \\mathbb{C}, senza casi";
        else if (map_count > 0) verdict.reason = "le relazioni d'ordine e i numeri reali non sono ancora trattati insieme alle applicazioni";
        else if (formula_has_kind(thesis, F_IN) || formula_has_kind(thesis, F_DIVIDES))
            verdict.reason = "le relazioni d'ordine e i numeri reali non sono ancora trattati insieme all'appartenenza a un insieme numerico e alla divisibilità";
        else if (has_parameter(thesis)) decide_with_parameter(thesis, &verdict);
        else {
            decide_by_signs(thesis, &verdict);
            sign_certify(thesis, &verdict);

            /* 40. La spiegazione, a verdetto dato: non lo cambia. */
            if (explanations_wanted) explain_signs(thesis, &verdict);
        }
        return verdict;
    }

    /* Quanti valori provare per ogni variabile nella verifica: dipende da
     * quanti quantificatori stanno uno dentro l'altro. */
    sample_width = width_for(quantifier_depth);

    /* Prima la tesi, poi la sua negazione. Il testo si riscrive da capo ogni
     * volta, perché comincia in modo diverso nei due casi. Anche la memoria
     * riparte da dov'era dopo il parsing: un primo tentativo che la riempie
     * non deve togliere al secondo la possibilità di riuscire.
     *
     * Con dei parametri (17s) la tesi e la negazione si cercano per ogni
     * valore dei parametri, che restano variabili generiche. Una tesi falsa
     * solo per qualche valore si smentisce però con quel valore: dopo i due
     * tentativi soliti, la negazione si cerca con i parametri legati, uno
     * dopo l'altro, ai primi PARAMETER_TRIES elementi del loro insieme. È
     * lecito perché ciò che l'enunciato afferma vale per ogni valore dei
     * parametri: basta che fallisca per uno, in cui le ipotesi valgono (le
     * regole definiscono un'applicazione, 18m), per smentirlo. */
    int stopped = 0, instances = 0;
    size_t parsed = arena_used;
    if (statement_parameter_count) instances = 1;
    for (int i = 0; i < statement_parameter_count; i++) instances *= PARAMETER_TRIES;
    for (int attempt = 0; attempt < 2 + instances && !syntax_error && !failure; attempt++) {
        int negated = attempt > 0, instance = attempt - 2;
        proof_reset();
        forget_choices(thesis);
        arena_used = parsed;
        atom_count = base_poly_count = atan_count = 0;
        chosen_count = 0;
        chosen_by_cases = 0;
        record_count = hypotheses_named = 0;
        if (universal_named) memset(universal_named, 0, universal_named_capacity);
        excluded_count = case_choice_count = region_depth = split_pending = 0;

        /* I parametri (17s) sono variabili generiche dall'inizio, oppure, in
         * uno degli ultimi tentativi, numeri. */
        env_count = 0;
        universal_count = 0;
        if (instance < 0)
            for (int i = 0; i < statement_parameter_count; i++) if (!universal_push(statement_parameters[i])) break;
        split_modulus = split_case = 0;
        search_left = MAX_SEARCH;
        proof_add("\\textbf{%s}\n\\begin{itemize}\n", negated ? "The statement is false." : "Proof.");
        for (int i = 0, rest = instance; i < statement_parameter_count && instance >= 0; i++, rest /= PARAMETER_TRIES) {
            Frac value[PARAMETER_TRIES];
            numbers_sample(statement_parameters[i].numbers, value, PARAMETER_TRIES);
            proof_add("\\item Take $%c = ", statement_parameters[i].name);
            put_frac(value[rest % PARAMETER_TRIES]);
            proof_add("$, an element of $");
            put_numbers(statement_parameters[i].numbers);
            proof_add("$.\n");
            choose(statement_parameters[i].name, value[rest % PARAMETER_TRIES]);
            env_push(statement_parameters[i].name, rat_frac(value[rest % PARAMETER_TRIES]));
        }

        /* 18m. Le regole definiscono davvero delle applicazioni? Se no, si
         * guarda sul campione se la regola è sbagliata o se è solo il
         * programma a non saperlo dimostrare. Il conto sul campione può
         * incontrare una divisione per zero, che qui è una risposta e non
         * un errore: per questo `failure` viene azzerato. */
        int defined = 1;
        for (int i = 0; i < map_count && defined; i++) {
            if (map_defined(&maps[i])) continue;

            /* Con i parametri legati a dei numeri le ipotesi possono non
             * valere per quei numeri: si passa ai successivi. */
            if (instance >= 0) { failure = NULL; defined = 0; continue; }
            int plausible = !failure && sample_with_parameters(NULL, 0, 0);
            failure = NULL;
            const char *fault = maps[i].cases && !plausible && !statement_parameter_count ? cases_fault(&maps[i]) : NULL;
            verdict.outcome = NOT_PROVED;
            verdict.reason = fault ? fault
                           : plausible ? "non riesco a dimostrare che la regola dà sempre un valore nel codominio"
                                       : "la regola non definisce un'applicazione: per qualche elemento del dominio il valore manca o cade fuori dal codominio";
            return verdict;
        }
        if (!defined) continue;

        /* Le regole del capitolo 18, con le potenze che fanno da lettere
         * (18x) solo finché cercano. */
        int found;
        power_letters = 1;
        if (negated) {
            proof_add("\\item \\emph{The conclusion fails.}\n\\begin{itemize}\n");
            found = establish_in_regions(thesis, 1, 0);
            proof_add("\\end{itemize}\n");
        } else {
            found = prove_claims(thesis);
        }
        power_letters = 0;
        /* Una ricerca che finisce i tentativi, o la memoria, è una ricerca
         * interrotta: non dice nulla sull'enunciato. */
        if (search_left <= 0 || failure == OUT_OF_MEMORY) stopped = 1;
        if (failure == OUT_OF_MEMORY) failure = NULL;
        else if (!found || failure) continue;
        if (!found) continue;
        proof_add("\\end{itemize}\n$\\Box$");

        /* Verifica indipendente: l'enunciato com'è scritto, quante prove
         * hanno trovato vere le ipotesi, i valori scelti da 18u-3 (vedi la
         * testa del capitolo 19). Come sopra, un errore di calcolo qui è una
         * mancata conferma. */
        sample_theses = 0;
        verification_left = verification_work_limit; verification_limited = 0;
        int confirmed = sample_with_parameters(thesis, negated, 0);
        const char *doubt = NULL;
        if (verification_limited) doubt = verification_problem;
        else if (failure || !confirmed) doubt = "la verifica indipendente, su un campione di numeri, non conferma la dimostrazione";
        else if (hypotheses_named && sample_theses < MIN_SATISFIED)
            doubt = "la verifica indipendente non ha trovato valori del campione che soddisfano le ipotesi, e quindi non ha controllato la tesi";
        else doubt = records_doubt();
        if (doubt) {
            failure = NULL;
            verdict.outcome = NOT_PROVED;
            verdict.reason = doubt;
        } else {
            verdict.outcome = negated ? REFUTED : PROVED;
            verdict.detail = negated ? describe_choices() : NULL;
            verdict.proof = proof_text;
            /* Le lettere di coppie le dicono già la dimostrazione e il
             * controesempio (17t-2); una lettera rinominata no. */
            if (unshadowed_note[0]) verdict.note = unshadowed_note;
        }
        return verdict;
    }

    /* 18r. Le regole che seguono la struttura non hanno deciso: se
     * l'enunciato è fatto solo di congruenze tra interi lo decide il conto
     * su tutti i resti. Viene dopo le altre perché, dove bastano, quelle
     * scrivono la dimostrazione passo per passo; e riparte da zero, perché
     * un loro conto uscito dai limiti non riguarda questo. */
    if (!syntax_error && !map_count) {
        const char *before = failure;
        failure = NULL;
        arena_used = parsed;
        atom_count = base_poly_count = atan_count = 0;
        env_count = universal_count = 0;
        if (decide_by_residues(thesis, &verdict)) return verdict;
        failure = before;
    }

    /* Notazione o conto fuori portata, oppure nessuna delle due prove
     * riuscita. */
    if (syntax_error || failure) {
        verdict.reason = syntax_error ? syntax_error : failure;
        return verdict;
    }
    verdict.outcome = NOT_PROVED;
    verdict.reason = stopped ? "la ricerca è stata interrotta: troppi tentativi senza arrivare a una dimostrazione"
                             : "le regole disponibili non bastano né a dimostrare né a smentire la tesi";
    return verdict;
}

/* Decide l'enunciato con quantificatori scritto in formula e ne ritorna il
 * verdetto, con la dimostrazione scritta.
 *
 * Se l'enunciato dichiara delle applicazioni deve avere la forma "ipotesi
 * implica tesi", con le dichiarazioni e le regole come ipotesi; altrimenti è
 * tutto tesi. Si prova a dimostrare la tesi e, se non riesce, la sua
 * negazione: nel primo caso il verdetto è DIMOSTRATO, nel secondo FALSO.
 *
 * Svuota l'arena e la tabella degli atomi: i risultati di chiamate precedenti
 * non sono più validi. */
static Verdict prove_quantified(const char *formula) {
    Verdict verdict = decide_quantified(formula);

    /* Le applicazioni dichiarate valgono solo per questo enunciato: il parser
     * delle espressioni, che serve anche agli altri metodi, non deve più
     * vederle (vedi `maps`, capitolo 8). Lo stesso per i parametri (17s). */
    map_count = statement_parameter_count = 0;
    return verdict;
}

/* 18v-8. LE APPLICAZIONI TRA NUMERI REALI: LA DEFINIZIONE SVOLTA
 *
 * A che cosa serve. "f(x) = x^{2} per x \ge 0, x(3 - x) per x < 0: f è
 * suriettiva su \mathbb{R}." Le regole 18a-18v lavorano sui razionali: tra i
 * reali la controimmagine di y è \sqrt{y}, che come valore di un "esiste" non
 * si scrive con un polinomio. Ma tra i reali c'è un'altra strada: tolta
 * l'applicazione, ciò che resta è un enunciato con confronti tra polinomi in
 * lettere reali, che la tabella dei segni decide da sola, con una lettera
 * (18p) o con due, una per parametro (18t, che proietta, divide la retta del
 * parametro in celle e ricontrolla la proiezione con un altro conto, 18t-h).
 * "Per ogni y esiste x con f(x) = y" diventa
 *
 *     \forall y\ \exists x\ ((x \ge 0 \land x^{2} = y) \lor (x < 0 \land x(3 - x) = y))
 *
 * e 18t trova, caso per caso su y, se l'insieme degli x è vuoto.
 *
 * Svolgere la definizione. Una condizione P in cui compare f(t), con f data
 * dai casi (c_i, e_i), vale esattamente quando vale una delle c_i(t) \land
 * P(e_i(t)): se i casi coprono il dominio, uno vale in t, e dove vale c_i è
 * f(t) = e_i(t) (lo dice l'ipotesi); viceversa, se valgono c_i(t) e P(e_i(t)),
 * è f(t) = e_i(t), quindi P(f(t)). Con una regola sola, f(t) è e(t). Si
 * svolge prima l'applicazione più interna, il cui argomento non ne contiene
 * altre. Le ipotesi su cui poggia lo svolgimento (i casi coprono il dominio,
 * dove si sovrappongono danno lo stesso valore, i valori stanno nel
 * codominio) sono anch'esse enunciati tra reali senza applicazioni, e le
 * decide prima la tabella dei segni.
 *
 * Il testo. Lo svolgimento si fa sugli alberi, e il risultato si scrive in
 * LaTeX (put_formula()) e si rilegge da capo, come ogni enunciato: è la via
 * di 17j, e la dimostrazione scritta cita ciò che è stato davvero dimostrato.
 * La tesi si divide nelle sue affermazioni, una congiunzione alla volta,
 * perché 18t vuole un parametro solo per enunciato.
 *
 * Che cosa si chiede. Applicazioni tra insiemi di reali, con regole e
 * condizioni che sono polinomi, o divise soltanto per numeri: dove
 * l'applicazione è definita, il valore svolto lo è sempre, e la tabella dei
 * segni non deve occuparsi di punti in cui un membro non esiste. Nessun
 * parametro, nessuna iterata. Le applicazioni a valori in coppie arrivano
 * già divise nelle loro componenti (17s). Di due argomenti ci sono solo
 * quelle di \mathbb{C}, che il lettore ha scritto come applicazioni di due
 * reali, la parte reale e la parte immaginaria (17s): con una regola sola,
 * senza casi, e il codominio senza estremi né punti tolti, perché le due
 * componenti del valore non hanno condizioni proprie.
 *
 * Gli "esiste" tra i reali (18v-11). Svolta la definizione, una parte può
 * avere più lettere di quante la tabella dei segni ne decida: per f di
 * \mathbb{C}, "f non è iniettiva" diventa "esistono a, A, b, B reali con ...",
 * quattro lettere. Se la parte comincia con degli "esiste" su tutto
 * \mathbb{R} (un "non per ogni" è un "esiste"), si danno loro i primi
 * razionali, e ciò che resta, con i numeri al posto delle lettere, è un
 * enunciato nuovo da decidere da capo: se è dimostrato, quei numeri sono i
 * valori degli "esiste", perché un razionale è un reale. È la regola 18j
 * portata tra i reali: prova degli esempi, e quando nessuno va bene la parte
 * resta non dimostrata, mai smentita, perché un esempio che manca tra i
 * primi razionali non dice nulla degli altri reali.
 *
 * Il certificato. Ogni enunciato svolto porta il suo, quando la tabella dei
 * segni lo scrive; l'enunciato con l'applicazione no, perché il passaggio
 * dall'uno agli altri, lo svolgimento, non è nella notazione dei
 * certificati: il verdetto lo dice.
 */

/* Ritorna 1 se in node ogni divisione è per un numero, senza lettere. */
static int divisions_by_numbers(const Node *node) {
    if (!node) return 1;
    if (node->kind == N_DIV && !node_is_numeral(node->b)) return 0;
    return divisions_by_numbers(node->a) && divisions_by_numbers(node->b) && divisions_by_numbers(node->c);
}

/* Ritorna un'applicazione di node il cui argomento non ne contiene altre, o
 * NULL se node non ne ha. */
static const Node *application_innermost(const Node *node) {
    if (!node) return NULL;
    const Node *inside = application_innermost(node->a);
    if (!inside) inside = application_innermost(node->b);
    if (!inside) inside = application_innermost(node->c);
    return inside ? inside : node->kind == N_APPLY ? node : NULL;
}

/* Ritorna una copia di f nell'arena, con le stesse componenti. */
static Formula *formula_copy(const Formula *f) {
    Formula *copy = formula_node(f->kind, NULL, NULL, f->start);
    *copy = *f;
    return copy;
}

/* Ritorna la congiunzione di a e b, o b se a è NULL. */
static Formula *conjoined(Formula *a, Formula *b) {
    if (!a) return b;
    Formula *both = formula_node(F_AND, a, b, NULL);
    both->start = both->end = NULL;
    return both;
}

/* 18v-8. Ritorna la condizione f con ogni applicazione svolta come descritto
 * in testa al paragrafo: un albero nuovo, nell'arena; NULL, con fail(), se
 * un'applicazione non si svolge: un'iterata, o una di due argomenti con dei
 * casi o scritta con un argomento solo. */
static Formula *applications_unfolded(const Formula *f) {
    if (!f || failure) return NULL;
    Formula *copy = formula_copy(f);
    if (f->a) copy->a = applications_unfolded(f->a);
    if (f->b) copy->b = applications_unfolded(f->b);

    /* Un confronto, un'appartenenza o una divisibilità: l'applicazione più
     * interna, poi di nuovo. */
    const Node *apply = application_innermost(f->left);
    if (!apply) apply = application_innermost(f->right);
    if (!apply) return copy;
    const Map *map = map_find(apply->name);
    if (!map || apply->c || (!map->body && !map->cases) || (map->binary && (map->cases || !apply->b))) {
        fail("un'applicazione che lo svolgimento non tratta");
        return NULL;
    }
    const Node *const argument[2] = {apply->a, apply->b};
    const int parameter[2] = {map->parameter, map->parameter2};
    int cases = map->cases ? map->cases : 1, arity = map->binary ? 2 : 1;
    Formula *any = NULL;
    for (int i = 0; i < cases && !failure; i++) {
        Node *value = node_substitute(map->cases ? map->piece[i].value : map->body, parameter, argument, arity);
        Formula *atom = formula_copy(f);
        atom->left = node_replaced(f->left, apply, value);
        atom->right = node_replaced(f->right, apply, value);
        Formula *piece = applications_unfolded(atom);
        if (map->cases) piece = conjoined(formula_substitute(map->piece[i].when, &map->parameter, argument, 1), piece);
        if (!any) { any = piece; continue; }
        Formula *either = formula_node(F_OR, any, piece, NULL);
        either->start = either->end = NULL;
        any = either;
    }
    return any;
}

/* Scrive la condizione f in LaTeX, dall'albero, con una parentesi intorno a
 * ogni parte: il testo si rilegge con la grammatica del capitolo 17. */
static void put_formula(const Formula *f) {
    static const char *const joint[] = {[F_AND] = "\\land", [F_OR] = "\\lor", [F_IMPLIES] = "\\implies", [F_IFF] = "\\iff"};
    switch (f->kind) {
    case F_EQUAL: case F_DISTINCT: case F_LESS: case F_LESS_EQ:
        put_node(f->left, 0);
        proof_add(f->kind == F_EQUAL ? " = " : f->kind == F_DISTINCT ? " \\neq " : f->kind == F_LESS ? " < " : " \\le ");
        put_node(f->right, 0);
        return;
    case F_IN:
        put_node(f->left, 0);
        proof_add(f->swapped ? " \\notin " : " \\in ");
        put_numbers(&f->numbers);
        return;
    case F_DIVIDES:
        put_node(f->left, 0);
        proof_add(f->swapped ? " \\nmid " : " \\mid ");
        put_node(f->right, 0);
        return;
    case F_NOT:
        proof_add("\\lnot (");
        put_formula(f->a);
        proof_add(")");
        return;
    case F_AND: case F_OR: case F_IMPLIES: case F_IFF:
        proof_add("(");
        put_formula(f->a);
        proof_add(") %s (", joint[f->kind]);
        put_formula(f->b);
        proof_add(")");
        return;
    case F_FORALL: case F_EXISTS: case F_SOLVE: {
        /* Una parte dei reali, con un estremo o dei punti tolti, diventa
         * \mathbb{R} con la condizione di appartenenza scritta con dei
         * confronti: "per ogni y in A vale P" è "per ogni reale y, y in A
         * implica P", "esiste" vuole y in A e P. La tabella dei segni, che
         * con due lettere le vuole su tutta la retta, le riceve così. */
        const NumberSet *set = &f->numbers;
        int part = set->reals && (set->bounded || set->holes);
        if (f->kind == F_SOLVE) proof_add("\\{%c \\in ", f->variable);
        else proof_add("%s %c \\in ", f->kind == F_FORALL ? "\\forall" : "\\exists", f->variable);
        if (part) proof_add("\\mathbb{R}");
        else put_numbers(set);
        proof_add(f->kind == F_SOLVE ? " \\mid " : "\\ (");
        if (part) {
            proof_add("(");
            if (set->bounded) proof_add("%c %s %lld", f->variable, set->strict ? ">" : "\\ge", set->low);
            for (int i = 0; i < set->holes; i++) {
                proof_add("%s%c \\neq ", set->bounded || i ? " \\land " : "", f->variable);
                put_frac(set->hole[i]);
            }
            proof_add(f->kind == F_FORALL ? ") \\implies (" : ") \\land (");
        }
        put_formula(f->a);
        if (part) proof_add(")");
        proof_add(f->kind == F_SOLVE ? "\\}" : ")");
        return;
    }
    default:
        fail("una condizione che lo svolgimento non sa scrivere");
    }
}

/* Mette in out, di size byte, il testo di f scritto da put_formula(), e
 * ritorna 1; 0 se non ci sta o se la scrittura non riesce. Il testo nasce
 * nella dimostrazione, che resta com'era. */
static int formula_text(const Formula *f, char *out, size_t size) {
    size_t start = proof_length;
    put_formula(f);
    size_t length = proof_length - start;
    int fits = length + 1 < size && !failure && proof_length + 1 < PROOF_BYTES;
    if (fits) {
        memcpy(out, proof_text + start, length);
        out[length] = 0;
    }
    proof_cut(start);
    return fits;
}

/* Ritorna 1 se l'espressione node è un polinomio, o una sua divisione per
 * numeri: un'espressione razionale definita ovunque. */
static int node_everywhere(const Node *node) { return term_is_rational(node) && divisions_by_numbers(node); }

/* Ritorna 1 se ogni condizione atomica di f confronta espressioni definite
 * ovunque. */
static int formula_everywhere(const Formula *f) {
    if (!f) return 1;
    return node_everywhere(f->left) && node_everywhere(f->right) && formula_everywhere(f->a) && formula_everywhere(f->b);
}

/* Ritorna 1 se le applicazioni dell'enunciato in corso sono di quelle che
 * 18v-8 svolge: tra insiemi di reali, con regole e condizioni definite
 * ovunque, senza parametri né iterate; di due argomenti solo quelle di
 * \mathbb{C} (non un'operazione scritta con un simbolo), senza casi e con il
 * codominio intero. */
static int real_maps_unfoldable(void) {
    if (!map_count || statement_parameter_count) return 0;
    for (int i = 0; i < map_count; i++) {
        const Map *map = &maps[i];
        if (map->iterates || !map->domain.reals || !map->codomain.reals) return 0;
        if (map->binary && (map->cases || map->codomain.bounded || map->codomain.holes || !map->second.reals || (map->name >= OPERATION_NAMES && map->name < GREEK_NAMES))) return 0;
        if (!map->cases && !node_everywhere(map->body)) return 0;
        for (int k = 0; k < map->cases; k++)
            if (!node_everywhere(map->piece[k].value) || !formula_everywhere(map->piece[k].when)) return 0;
    }
    return 1;
}

/* Il nodo del numero razionale v. */
static Node *node_of_frac(Frac v) {
    Node *size = v.den == 1 ? node_num(llabs(v.num)) : node_new(N_DIV, node_num(llabs(v.num)), node_num(v.den));
    return v.num < 0 ? node_new(N_NEG, size, NULL) : size;
}

/* Ritorna "\forall x \in A\ (body)", con x e A la variabile e il dominio di
 * map. */
static Formula *over_domain(const Map *map, Formula *body) {
    Formula *all = formula_node(F_FORALL, body, NULL, NULL);
    all->start = all->end = NULL;
    all->variable = map->parameter;
    all->numbers = map->domain;
    return all;
}

/* Le affermazioni di 18v-8, in testo: le ipotesi su cui poggia lo
 * svolgimento, e le parti della tesi svolte. */
typedef struct {
    int count;                        /* quante, in text[] */
    int definitions;                  /* le prime: le ipotesi sulle definizioni */
    char text[MAX_UNFOLDINGS][MAX_FORMULA];
    const char *source[MAX_UNFOLDINGS];  /* le parti della tesi come sono scritte; per un'ipotesi, che cosa dice */
    size_t length[MAX_UNFOLDINGS];
    int letters[MAX_UNFOLDINGS];         /* 18v-11: le lettere degli "esiste" in testa alla parte, in letter[] */
    int letter[MAX_UNFOLDINGS][MAX_WITNESS_LETTERS];
    char rest[MAX_UNFOLDINGS][MAX_FORMULA];  /* e ciò che segue, con le negazioni portate dentro */
} Unfolded;

/* Aggiunge f, scritta, alle affermazioni u; ritorna 0 se non c'è posto. */
static int unfolded_add(Unfolded *u, const Formula *f, const char *source, size_t length) {
    if (u->count == (int)(sizeof u->text / sizeof *u->text) || !formula_text(f, u->text[u->count], MAX_FORMULA)) return 0;
    u->source[u->count] = source;
    u->length[u->count++] = length;
    return 1;
}

/* 18v-11. Mette in u, per l'ultima parte aggiunta, le lettere degli
 * "esiste" su tutto \mathbb{R} con cui comincia f (letta negata se negated:
 * un "non per ogni" è un "esiste"), al più MAX_WITNESS_LETTERS, e il testo di
 * ciò che segue, con la negazione portata davanti. */
static int witness_prefix(Unfolded *u, const Formula *f, int negated) {
    int k = u->count - 1, count = 0;
    for (;;) {
        if (f->kind == F_NOT) { negated = !negated; f = f->a; continue; }
        int exists = (f->kind == F_EXISTS) != negated && (f->kind == F_EXISTS || f->kind == F_FORALL);
        if (!exists || !f->numbers.reals || f->numbers.bounded || f->numbers.holes || count == MAX_WITNESS_LETTERS) break;
        u->letter[k][count++] = f->variable;
        f = f->a;
    }
    u->letters[k] = count;
    if (!count) return 1;
    char *rest = u->rest[k];
    size_t used = 0;
    if (negated) { strcpy(rest, "\\lnot ("); used = strlen(rest); }
    if (!formula_text(f, rest + used, MAX_FORMULA - used - 2)) return 0;
    if (negated) strcat(rest, ")");
    return 1;
}

/* Aggiunge a u le parti della congiunzione f, svolte. */
static int claims_unfolded(Unfolded *u, const Formula *f) {
    if (f->kind == F_AND) return claims_unfolded(u, f->a) && claims_unfolded(u, f->b);
    Formula *plain = applications_unfolded(f);
    return plain && unfolded_add(u, plain, f->start, (size_t)(f->end - f->start)) && witness_prefix(u, plain, 0);
}

/* 18v-11. Prova a dimostrare la parte k di u, che comincia con degli
 * "esiste" tra i reali, dando a ognuno un razionale: i primi elementi di
 * \mathbb{Q}, tanti quanti le lettere permettono. Ciò che segue, con i numeri
 * al posto delle lettere, si riscrive (draft_rewrite()) e si decide da capo:
 * se è dimostrato, quei numeri sono i valori degli "esiste", e la parte è
 * dimostrata, perché un razionale è un reale. Ritorna il verdetto della
 * prima scelta dimostrata, o uno con outcome NOT_PROVED; in *values le
 * scelte, scritte. */
static Verdict witnesses_tried(const Unfolded *u, int k, char *values, size_t size) {
    Verdict none = {NOT_PROVED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    int letters = u->letters[k], width = letters <= 2 ? 5 : 3;
    Frac sample[5];
    numbers_sample(&(NumberSet){.reals = 0}, sample, width);
    long long combinations = 1;
    for (int i = 0; i < letters; i++) combinations *= width;
    for (long long c = 0; c < combinations; c++) {
        char number[MAX_WITNESS_LETTERS][48];
        const char *to[MAX_WITNESS_LETTERS];
        size_t written = 0;
        for (long long i = 0, rest = c; i < letters; i++, rest /= width) {
            Frac v = sample[rest % width];
            if (v.den == 1) snprintf(number[i], sizeof number[i], "(%lld)", v.num);
            else snprintf(number[i], sizeof number[i], "(%s\\frac{%lld}{%lld})", v.num < 0 ? "-" : "", llabs(v.num), v.den);
            to[i] = number[i];
            written += (size_t)snprintf(values + written, size > written ? size - written : 0, "%s%c = %s", i ? ", " : "", u->letter[k][i], number[i]);
        }

        /* Il testo con i numeri: nasce nella bozza del lettore. */
        static char closed[MAX_FORMULA];
        syntax_error = NULL;
        draft_length = 0;
        draft_rewrite(u->rest[k], u->rest[k] + strlen(u->rest[k]), u->letter[k], to, letters);
        if (syntax_error || draft_length >= sizeof closed) { syntax_error = NULL; continue; }
        memcpy(closed, draft, draft_length);
        closed[draft_length] = 0;
        Verdict tried = prove_quantified(closed);
        if (tried.outcome == PROVED) return tried;
    }
    return none;
}

/* Aggiunge a u, per ogni applicazione, gli enunciati tra reali che dicono
 * che la sua definizione dà un valore, uno solo, nel codominio: i casi
 * coprono il dominio, dove due valgono insieme i valori coincidono, e ogni
 * valore sta sopra l'estremo del codominio e lontano dai suoi punti tolti. */
static int definitions_unfolded(Unfolded *u) {
    for (int i = 0; i < map_count; i++) {
        const Map *map = &maps[i];
        const NumberSet *to = &map->codomain;
        int cases = map->cases ? map->cases : 1;
        if (map->cases) {
            Formula *cover = NULL;
            for (int k = 0; k < map->cases; k++) {
                if (!cover) { cover = (Formula *)map->piece[k].when; continue; }
                Formula *either = formula_node(F_OR, cover, (Formula *)map->piece[k].when, NULL);
                either->start = either->end = NULL;
                cover = either;
            }
            if (!unfolded_add(u, over_domain(map, cover), "The cases cover the domain", 0)) return 0;
            for (int j = 0; j < map->cases; j++)
                for (int k = j + 1; k < map->cases; k++) {
                    Formula *same = formula_node(F_EQUAL, NULL, NULL, NULL), *both = conjoined((Formula *)map->piece[j].when, (Formula *)map->piece[k].when);
                    same->start = same->end = NULL;
                    same->left = map->piece[j].value;
                    same->right = map->piece[k].value;
                    Formula *agree = formula_node(F_IMPLIES, both, same, NULL);
                    agree->start = agree->end = NULL;
                    if (!unfolded_add(u, over_domain(map, agree), "Where two cases hold together, they give the same value", 0)) return 0;
                }
        }
        if (!to->bounded && !to->holes) continue;
        for (int k = 0; k < cases; k++) {
            Node *value = map->cases ? map->piece[k].value : map->body;
            Formula *inside = NULL;
            if (to->bounded) {
                inside = formula_node(to->strict ? F_LESS : F_LESS_EQ, NULL, NULL, NULL);
                inside->left = node_num(to->low);
                inside->right = value;
            }
            for (int h = 0; h < to->holes; h++) {
                Formula *away = formula_node(F_DISTINCT, NULL, NULL, NULL);
                away->left = value;
                away->right = node_of_frac(to->hole[h]);
                inside = conjoined(inside, away);
            }
            if (map->cases) {
                inside = formula_node(F_IMPLIES, (Formula *)map->piece[k].when, inside, NULL);
            }
            if (!unfolded_add(u, over_domain(map, inside), "The values lie in the codomain", 0)) return 0;
        }
    }
    u->definitions = u->count;
    return 1;
}

/* 18v-8. Decide la tesi thesis, di un enunciato con applicazioni tra reali
 * che real_maps_unfoldable() accetta, svolgendo le definizioni come
 * descritto in testa al paragrafo, e ne ritorna il verdetto. Ogni enunciato
 * svolto si decide da capo con prove_quantified(): al ritorno le
 * applicazioni e gli alberi dell'enunciato non valgono più. */
static Verdict decide_real_maps(const Formula *thesis) {
    static Unfolded u;
    static char composed[PROOF_BYTES], counterexample[400];
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, "con la tabella dei segni, sulla definizione svolta", NULL, NULL};
    verdict.reason = "la definizione svolta non si scrive: troppo lunga, o con applicazioni che lo svolgimento non tratta";

    /* I testi, tutti prima di decidere il primo: ogni decisione riparte da
     * zero, e gli alberi non varrebbero più. Il controesempio di un
     * enunciato precedente non vale per questo: prima restava, e un
     * enunciato falso per un'altra ragione lo riportava (fuzz_cases.py). */
    static char reading[200];
    u.count = u.definitions = 0;
    counterexample[0] = 0;
    snprintf(reading, sizeof reading, "%s", pairs_note);
    if (!definitions_unfolded(&u) || !claims_unfolded(&u, thesis) || failure) { failure = NULL; return verdict; }

    /* Le ipotesi della definizione devono valere; le parti della tesi tutte
     * valere, o una fallire. */
    size_t length = 0;
    int refuted = -1;
    for (int k = 0; k < u.count && refuted < 0; k++) {
        static char values[400];
        Verdict part = prove_quantified(u.text[k]);
        int definition = k < u.definitions, witnessed = 0;
        if (!definition && part.outcome != PROVED && part.outcome != REFUTED && u.letters[k]) {
            Verdict tried = witnesses_tried(&u, k, values, sizeof values);
            if (tried.outcome == PROVED) { part = tried; witnessed = 1; }
        }
        if (part.outcome == REFUTED && !definition) {
            refuted = k;
            if (part.detail) snprintf(counterexample, sizeof counterexample, "%s", part.detail);
        } else if (part.outcome != PROVED) {
            verdict.outcome = part.outcome == UNSUPPORTED ? UNSUPPORTED : NOT_PROVED;
            verdict.reason = definition ? (part.outcome == REFUTED ? "la definizione per casi non definisce un'applicazione: la tabella dei segni lo smentisce"
                                                                    : "non riesco a dimostrare che la definizione dà un valore, uno solo, nel codominio")
                                        : part.reason;
            return verdict;
        }

        /* La sua dimostrazione, dopo il titolo, nel testo che si compone. */
        if (!part.proof) continue;
        int n = 0;
        if (definition) n = snprintf(composed + length, sizeof composed - length, "\\item \\emph{%s:} $%s$.\n\n%s\n", u.source[k], u.text[k], part.proof);
        else if (witnessed)
            n = snprintf(composed + length, sizeof composed - length, "\\item \\emph{Claim:} $%.*s$, that is, with the definition unfolded, $%s$. "
                         "It holds with the rational values $%s$, which are real numbers: with them in place of the letters,\n\n%s\n",
                         (int)u.length[k], u.source[k], u.text[k], values, part.proof);
        else n = snprintf(composed + length, sizeof composed - length, "\\item \\emph{Claim:} $%.*s$, that is, with the definition unfolded, $%s$.\n\n%s\n",
                          (int)u.length[k], u.source[k], u.text[k], part.proof);
        if (n < 0 || (size_t)n >= sizeof composed - length) { verdict.reason = "dimostrazione troppo lunga"; return verdict; }
        length += (size_t)n;
    }

    /* Il verdetto, e la dimostrazione: le parti, dentro un elenco. */
    proof_reset();
    proof_add(refuted >= 0 ? "\\textbf{The statement is false.} " : "\\textbf{Proof.} ");
    proof_add("Each value $f(t)$ is replaced by its definition: by the value of the case that holds in $t$, joined to its condition. "
              "The statements without the map are decided by the sign table.\n\\begin{itemize}\n");
    if (proof_length + length + 64 >= PROOF_BYTES) { verdict.reason = "dimostrazione troppo lunga"; return verdict; }
    proof_add("%s\\end{itemize}\n%s", composed, refuted >= 0 ? "" : "$\\Box$");
    verdict.outcome = refuted >= 0 ? REFUTED : PROVED;
    verdict.reason = "lo svolgimento della definizione non è nella notazione dei certificati";
    verdict.detail = refuted >= 0 && counterexample[0] ? counterexample : NULL;
    verdict.proof = proof_text;
    verdict.note = reading[0] ? reading : NULL;
    return verdict;
}

