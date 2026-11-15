/* =============================================================================
 * 38. IDENTITÀ CON GLI INDICI: IL CONTO SU TUTTI I VALORI
 * ============================================================================
 *
 * Un'identità con gli indici, letta dal capitolo 37 di parser.c, dice: per
 * ogni scelta dei tensori che nomina, e per ogni valore da 1 a d di ciascun
 * indice libero, i due membri sono uguali, con gli indici ripetuti sommati
 * da 1 a d. Gli indici liberi hanno un numero finito di valori: l'enunciato
 * si decide provandoli tutti. È una decisione, non un tentativo: risponde
 * sia quando è vero sia quando è falso.
 *
 *   38a. I valori. In un punto (una scelta dei valori degli indici liberi)
 *        la delta vale 0 o 1, il simbolo di Levi-Civita 0, 1 o -1, e una
 *        componente di un tensore qualsiasi è una lettera di cui non si sa
 *        nulla: un atomo (capitolo 4), uno per componente. Ogni membro è
 *        allora un polinomio negli atomi (capitolo 5), e i due membri sono
 *        uguali per ogni scelta dei tensori esattamente quando la loro
 *        differenza è il polinomio nullo (capitolo 12). Il verso che non è
 *        ovvio: un polinomio che vale zero per ogni valore reale delle sue
 *        lettere non ha termini. Con una lettera, perché un polinomio non
 *        nullo ha un numero finito di radici; con più lettere, per induzione,
 *        guardandolo come polinomio nell'ultima con le altre fissate. Quindi
 *        due polinomi diversi danno davvero un controesempio: dei tensori
 *        per cui i due membri sono diversi.
 *
 *   38b. I prodotti. I fattori di un prodotto, anche scritto con più
 *        parentesi, si raccolgono in un solo elenco, con tutte le lettere
 *        che la convenzione somma in quel prodotto (index_prepare()).
 *
 *   38c. Le somme. Si dà un valore a una lettera sommata alla volta, e si
 *        salta ciò che vale zero senza calcolarlo: una delta (o una metrica
 *        dichiarata, che è diagonale) con un indice già noto fissa l'altro
 *        (la somma su j di \delta_{ij} a_{j} è a_{i}, perché gli addendi
 *        con j diverso da i sono nulli), e un simbolo di Levi-Civita con
 *        due indici uguali annulla tutto il ramo. Si saltano solo addendi
 *        nulli, quindi la somma è la stessa.
 *
 *   38d. La decisione: tutti i punti, uno dopo l'altro; il primo in cui i
 *        due membri sono diversi è il controesempio.
 *
 *   38e. Il certificato, che il verificatore indipendente ricontrolla
 *        (capitolo 19 di checker.c). Lui non salta nulla: somma tutti gli
 *        addendi, anche i nulli, con i suoi polinomi, nel nodo in cui ogni
 *        lettera è sommata e non su un elenco di fattori. I due conti sono
 *        diversi, e coincidono solo se sono giusti tutti e due. Questo
 *        linguaggio è coperto per intero dai certificati: il verdetto è
 *        DIMOSTRATO o FALSO solo con il certificato accettato. Se il
 *        verificatore non arriva in fondo (troppe componenti, budget
 *        finito) il verdetto è NON DIMOSTRATO, e dice perché.
 *
 *   38f. Ciò che si scrive: i valori dei due membri nel controesempio, e in
 *        un punto d'esempio della dimostrazione, sono riletti dal capitolo
 *        37 e ricalcolati (index_reread()). Con una metrica le componenti
 *        sono scritte con gli indici dove l'enunciato li dichiara, A^{1}
 *        B_{1}, e la rilettura controlla anche questo. Qui dentro i valori
 *        degli indici vanno sempre da 1 a d; se l'enunciato li conta da 0
 *        (37d in parser.c) è solo chi scrive a tenerne conto: un valore v
 *        è scritto v + origin - 1, nel punto del controesempio e negli
 *        indici delle componenti. Nel certificato restano da 1 a d. Un
 *        indice greco è scritto con la sua lettera greca
 *        (IndexStatement.label); nel certificato con la lettera latina che
 *        lo rappresenta (37f).
 *
 *   38g. Le componenti date (39d in parser.c). Un tensore che un'ipotesi dà
 *        con una tabella o con un elenco non è un atomo: in un punto vale
 *        il polinomio del suo elemento di quel posto, negli atomi dei
 *        tensori qualsiasi che l'elemento nomina (index_leaf()). Il resto
 *        del conto non cambia, e l'enunciato vale per ogni scelta dei
 *        tensori che restano qualsiasi. Nel certificato le componenti vanno
 *        come dati, una voce given per tensore, e il verificatore le
 *        sostituisce per conto suo: che la tabella sia stata letta bene
 *        (righe e colonne, posizioni) non lo vede nemmeno lui, perché riceve
 *        gli elementi già letti. Lo vedono i test e l'oracolo del fuzz, che
 *        ha un lettore suo.
 *
 *   38h. La metrica con funzioni delle coordinate (39f in parser.c). Gli
 *        elementi della diagonale sono frazioni di polinomi nelle lettere
 *        delle coordinate, e g^{ii} è la frazione rovesciata. Il valore di
 *        un membro in un punto è allora una frazione di polinomi (Rat,
 *        capitolo 7), e due valori sono uguali quando lo è il prodotto in
 *        croce dei loro numeratori e denominatori (index_same()): non si
 *        divide mai. L'uguaglianza così stabilita vale dove i denominatori
 *        non si annullano, cioè dove gli elementi della metrica sono
 *        definiti e diversi da zero: lo dicono il verdetto e la
 *        dimostrazione. Un elemento che è il polinomio nullo non ha quel
 *        "dove", e l'enunciato è rifiutato. Con una metrica di numeri i
 *        denominatori sono tutti 1, e il conto è quello di prima. I valori
 *        di un controesempio si scrivono solo quando sono polinomi.
 *
 * Il lavoro (i punti e gli addendi visitati) è contato contro il budget di
 * --model-steps, lo stesso da cui viene quello dato al verificatore
 * (checker_steps()): un conto troppo lungo finisce con NON DIMOSTRATO.
 *
 * Perché non le regole che si usano a mano (\varepsilon\varepsilon =
 * \delta\delta - \delta\delta, la delta che sostituisce un indice). Portano
 * a una forma più semplice, ma non decidono: in dimensione fissa ci sono
 * identità che nessuna di quelle regole vede (in dimensione 2 è nulla ogni
 * espressione antisimmetrica in tre indici), e riconoscere due prodotti
 * uguali a meno del nome degli indici sommati è un problema a sé. Il conto
 * diretto è più semplice, è completo, e per gli esercizi costa poco: sei
 * indici in dimensione 3 sono 729 casi.
 */

/* Da dove cominciano, tra gli atomi VAR, i "nomi" delle componenti dei
 * tensori: non sono caratteri, quindi non si confondono con le lettere
 * degli altri enunciati. La componente di posto p del tensore la cui
 * lettera ha posto s (index_slot()) ha nome INDEX_ATOMS + p INDEX_LETTERS
 * + s, e deve stare in un int: p è al più INDEX_PLACES. */
#define INDEX_ATOMS 256
#define INDEX_PLACES ((INT_MAX - INDEX_ATOMS) / INDEX_LETTERS - 1)

/* L'enunciato in corso: la dimensione; il rango del tensore di ogni lettera
 * (IndexStatement.rank); l'enunciato stesso, per la metrica e per ciò che è
 * dichiarato di \varepsilon e delle posizioni degli indici (capitolo 39 di
 * parser.c: metric è NULL senza metrica); il lavoro fatto; 1 se il budget è
 * finito. */
static int index_dimension;
static const int *index_ranks;
static const IndexStatement *index_statement;
static long long index_work;
static int index_stopped;

/* Ritorna il valore dell'indice entry di un simbolo: il numero scritto, o il
 * valore che value[] dà alla sua lettera. */
static int index_at(int entry, const int *value) { return entry < 'A' ? entry : value[index_slot(entry)]; }

static Rat index_value(IndexNode *node, int *value);

/* 38h. La metrica dell'enunciato in corso: per ogni valore i da 1 a d di un
 * indice, index_lower[i - 1] è g_{ii} e index_upper[i - 1] è g^{ii}, la sua
 * inversa, come frazioni di polinomi nelle lettere degli elementi (numeri,
 * per una metrica di numeri). Li prepara index_metric_values(), nell'arena;
 * senza metrica non si usano. */
static Rat *index_lower, *index_upper;

/* 38h. Ritorna il polinomio 1 senza prendere memoria dall'arena: è il
 * denominatore di quasi tutti i valori, e viene chiesto a ogni simbolo. */
static Poly index_one(void) {
    static Term one;
    one.coef = num_int(1);
    one.mono.count = 0;
    return (Poly){1, &one};
}

/* 38h. Ritorna la frazione 1 se unit non è zero, altrimenti la frazione 0,
 * senza prendere memoria. */
static Rat index_whole(int unit) { return (Rat){unit ? index_one() : (Poly){0, NULL}, index_one()}; }

/* 38h. Ritorna a b. Se i due denominatori sono 1 moltiplica solo i
 * numeratori: è il caso di ogni metrica di numeri, e il conto costa quanto
 * costava prima che i valori fossero frazioni. */
static Rat index_times(Rat a, Rat b) {
    if (poly_is_one(a.den) && poly_is_one(b.den)) return (Rat){poly_mul(a.num, b.num), a.den};
    return rat_mul(a, b);
}

/* 38h. Ritorna 1 se le frazioni a e b sono uguali dove i loro denominatori
 * non si annullano: lo sono esattamente quando il prodotto in croce
 * a.num b.den - b.num a.den è il polinomio nullo (capitolo 12). I
 * denominatori non sono mai il polinomio nullo (capitolo 7). */
static int index_same(Rat a, Rat b) {
    return poly_vanishes(poly_add(poly_mul(a.num, b.den), poly_mul(b.num, a.den), 1));
}

/* 38h. Ritorna 1 se la frazione r è un polinomio che si sa scrivere: il
 * denominatore è 1 e ogni esponente è un intero positivo. Un denominatore
 * di un solo termine il capitolo 7 lo porta al numeratore con gli esponenti
 * negativi: non è un polinomio nemmeno quello. */
static int index_plain(Rat r) {
    if (!poly_is_one(r.den)) return 0;
    for (int i = 0; i < r.num.count; i++)
        for (int f = 0; f < r.num.term[i].mono.count; f++)
            if (r.num.term[i].mono.factor[f].exp.den != 1 || r.num.term[i].mono.factor[f].exp.num < 1) return 0;
    return 1;
}

/* 38a. Ritorna il valore del simbolo leaf, con le sue lettere ai valori di
 * value[]: un numero per la delta e per il simbolo di Levi-Civita, l'atomo
 * della componente per un tensore qualsiasi, il polinomio dell'elemento per
 * un tensore dato per componenti (38g). Con una metrica di funzioni è una
 * frazione di polinomi (38h); altrimenti il denominatore è 1.
 *
 * Il simbolo di Levi-Civita ha d indici, con valori da 1 a d. Se due
 * coincidono vale 0. Altrimenti sono una permutazione di (1, ..., d), e
 * vale il suo segno: 1 se si riporta in ordine con un numero pari di scambi,
 * -1 se dispari. Quella parità è la stessa del numero delle coppie fuori
 * ordine (due posti i < j con il valore in i maggiore di quello in j),
 * perché uno scambio di due posti vicini ne cambia il numero di uno.
 *
 * Con una metrica dichiarata (capitolo 39 di parser.c), diagonale con gli
 * elementi c_1, ..., c_d. La metrica vale c_i con due indici uguali in basso,
 * 1/c_i con due uguali in alto, 1 con uno e uno, e 0 con due indici diversi.
 * \varepsilon vale, nella posizione in cui è dichiarato, il valore
 * dichiarato per il segno della permutazione. Un indice scritto in una
 * posizione diversa da quella dichiarata (per \varepsilon dall'ipotesi, per
 * un tensore dalla sua prima occorrenza) è stato alzato o abbassato: se vale
 * i, la componente è moltiplicata per 1/c_i se è stato alzato, per c_i se è
 * stato abbassato, perché la metrica è diagonale e nella contrazione g^{ij}
 * T_{j} resta il solo addendo j = i. È così che si calcola l'identità com'è
 * scritta; in quella svolta (39c) ogni indice è al suo posto, e questi
 * fattori non ci sono. */
static Rat index_leaf(const IndexNode *leaf, const int *value) {
    const Rat zero = index_whole(0);
    const IndexStatement *s = index_statement;
    if (leaf->kind == IX_DELTA) return index_at(leaf->index[0], value) == index_at(leaf->index[1], value) ? index_whole(1) : zero;
    if (leaf->kind == IX_METRIC || leaf->kind == IX_LOWER || leaf->kind == IX_UPPER) {
        int x = index_at(leaf->index[0], value);
        if (x != index_at(leaf->index[1], value)) return zero;
        if (leaf->kind == IX_METRIC && leaf->upper[0] != leaf->upper[1]) return index_whole(1);
        return leaf->kind == IX_UPPER || (leaf->kind == IX_METRIC && leaf->upper[0]) ? index_upper[x - 1] : index_lower[x - 1];
    }

    /* Gli indici spostati dalla posizione dichiarata. */
    Rat moved = index_whole(1);
    for (int i = 0; s->metric && i < leaf->rank; i++) {
        int declared = leaf->kind == IX_EPSILON ? s->epsilon_upper : s->reference[index_slot(leaf->name)][i];
        int x = index_at(leaf->index[i], value);
        if (leaf->upper[i] != declared) moved = index_times(moved, leaf->upper[i] ? index_upper[x - 1] : index_lower[x - 1]);
    }
    if (leaf->kind == IX_EPSILON) {
        int sign = 1;
        for (int i = 0; i < leaf->rank; i++)
            for (int j = i + 1; j < leaf->rank; j++) {
                int x = index_at(leaf->index[i], value), y = index_at(leaf->index[j], value);
                if (x == y) return zero;
                if (x > y) sign = -sign;
            }
        return index_times(moved, (Rat){poly_const(num_frac(frac_mul(s->metric ? s->epsilon : frac_int(1), frac_int(sign)))), index_one()});
    }

    /* Il posto della componente tra quelle del tensore: gli indici meno uno,
     * come cifre in base d. */
    long long place = 0;
    for (int i = 0; i < leaf->rank; i++) {
        int digit = index_at(leaf->index[i], value) - 1;
        if (place > (INDEX_PLACES - digit) / index_dimension) { fail("un tensore ha troppe componenti"); return zero; }
        place = place * index_dimension + digit;
    }

    /* 38g. Un tensore dato: il suo elemento di quel posto, per i fattori
     * degli indici spostati. L'elemento non ha lettere tra gli indici, e un
     * punto qualsiasi gli va bene. */
    IndexNode **given = s->given[index_slot(leaf->name)];
    if (given) {
        int none[INDEX_LETTERS] = {0};
        return index_times(moved, index_value(given[place], none));
    }
    Term component;
    component.coef = num_int(1);
    component.mono = mono_atom(atom_var(INDEX_ATOMS + (int)place * INDEX_LETTERS + index_slot(leaf->name)), frac_int(1));
    return index_times(moved, (Rat){poly_term(component), index_one()});
}

/* 38b. Mette in list, se non è NULL, i fattori del prodotto che comincia in
 * node, scendendo nei prodotti e fermandosi a ciò che non lo è; ne aggiunge
 * il numero a *count, e a *sum le lettere che la convenzione somma in quel
 * prodotto: quelle dei suoi nodi prodotto e quelle ripetute dentro un suo
 * simbolo, come la i di \delta_{ii}. */
static void index_collect(IndexNode *node, IndexNode **list, int *count, IndexSet *sum) {
    if (node->kind == IX_MUL) {
        *sum |= node->here;
        index_collect(node->a, list, count, sum);
        index_collect(node->b, list, count, sum);
        return;
    }
    if (index_is_leaf(node)) *sum |= node->here;
    if (list) list[*count] = node;
    ++*count;
}

/* 38b. Prepara il sottoalbero node per il conto: a ogni prodotto, e a ogni
 * simbolo che non sta in un prodotto, annota l'elenco dei fattori e le
 * lettere da sommare (factor, factors, sum). Un simbolo da solo è un
 * prodotto di un fattore. Se l'arena è piena lo dice `failure`. */
static void index_prepare(IndexNode *node) {
    if (node->kind == IX_NUM) return;
    if (node->kind == IX_NEG || node->kind == IX_ADD || node->kind == IX_SUB) {
        index_prepare(node->a);
        if (node->b) index_prepare(node->b);
        return;
    }

    /* Due passate: prima quanti sono i fattori, poi l'elenco. */
    int count = 0;
    IndexSet sum = 0;
    index_collect(node, NULL, &count, &sum);
    node->factor = arena_alloc(sizeof *node->factor * (size_t)count);
    if (!node->factor) return;
    count = 0;
    index_collect(node, node->factor, &count, &sum);
    node->factors = count;
    node->sum = sum;

    /* I fattori che sono somme tra parentesi hanno dentro altri prodotti. */
    for (int i = 0; i < count; i++)
        if (!index_is_leaf(node->factor[i])) index_prepare(node->factor[i]);
}

/* 38c. Ritorna la somma, sui valori da 1 a d delle lettere di open, del
 * prodotto dei fattori di node (index_prepare()); le altre lettere hanno già
 * il loro valore in value[], dove vengono scritti quelli delle lettere di
 * open. Ogni chiamata conta nel lavoro; finito il budget annota
 * index_stopped, e il valore ritornato non conta. */
static Rat index_contract(IndexNode *node, IndexSet open, int *value) {
    const Rat zero = index_whole(0);
    if (failure || index_stopped) return zero;
    if (++index_work > model_step_limit) { index_stopped = 1; return zero; }

    /* Ciò che i simboli dicono già con le lettere note: un fattore nullo
     * annulla il ramo, e una delta con un solo indice ancora da sommare ne
     * fissa il valore. */
    int fixed = -1, fixed_value = 0;
    for (int f = 0; f < node->factors; f++) {
        const IndexNode *leaf = node->factor[f];
        if (leaf->kind == IX_DELTA || leaf->kind == IX_METRIC || leaf->kind == IX_LOWER || leaf->kind == IX_UPPER) {
            int x = leaf->index[0], y = leaf->index[1];
            int x_open = x >= 'A' && (open >> index_slot(x) & 1), y_open = y >= 'A' && (open >> index_slot(y) & 1);
            if (!x_open && !y_open) {
                if (index_at(x, value) != index_at(y, value)) return zero;
            } else if (x_open != y_open && fixed < 0) {
                fixed = index_slot(x_open ? x : y);
                fixed_value = index_at(x_open ? y : x, value);
            }
        } else if (leaf->kind == IX_EPSILON) {
            for (int i = 0; i < leaf->rank; i++)
                for (int j = i + 1; j < leaf->rank; j++) {
                    int x = leaf->index[i], y = leaf->index[j];
                    if ((x >= 'A' && (open >> index_slot(x) & 1)) || (y >= 'A' && (open >> index_slot(y) & 1))) continue;
                    if (index_at(x, value) == index_at(y, value)) return zero;
                }
        }
    }

    /* Tutte le lettere hanno un valore: il prodotto dei fattori. */
    if (!open) {
        Rat product = index_whole(1);
        for (int f = 0; f < node->factors && product.num.count; f++) {
            IndexNode *factor = node->factor[f];
            product = index_times(product, index_is_leaf(factor) ? index_leaf(factor, value) : index_value(factor, value));
        }
        return product;
    }

    /* La lettera fissata da una delta ha un valore solo; un'altra li prova
     * tutti. */
    if (fixed >= 0) {
        value[fixed] = fixed_value;
        return index_contract(node, open & ~(1ULL << fixed), value);
    }
    int slot = index_first_slot(open);
    Rat total = zero;
    for (int v = 1; v <= index_dimension; v++) {
        value[slot] = v;
        Rat addend = index_contract(node, open & ~(1ULL << slot), value);
        if (addend.num.count) total = rat_add(total, addend, 0);
    }
    return total;
}

/* Ritorna il valore di node nel punto value[]: un polinomio nelle
 * componenti dei tensori (38a), o una frazione di polinomi con una metrica
 * di funzioni (38h). Le lettere libere di node hanno il loro valore in
 * value[]; quelle sommate lo ricevono in index_contract(). node è stato
 * preparato da index_prepare(). */
static Rat index_value(IndexNode *node, int *value) {
    if (node->kind == IX_NUM) return (Rat){poly_const(num_frac(node->number)), index_one()};
    if (node->kind == IX_NEG) return rat_add(index_whole(0), index_value(node->a, value), 1);
    if (node->kind == IX_ADD || node->kind == IX_SUB) {
        Rat left = index_value(node->a, value);
        return rat_add(left, index_value(node->b, value), node->kind == IX_SUB);
    }
    return index_contract(node, node->sum, value);
}

/* 38h. Prepara index_lower[] e index_upper[] per l'enunciato s, che ha una
 * metrica: i suoi elementi e i loro inversi. Ritorna 0, con il motivo in
 * *why, se un elemento o il suo denominatore è il polinomio nullo: la
 * metrica non sarebbe invertibile in nessun punto. Gli alberi degli
 * elementi sono già stati preparati (index_prepare()). */
static int index_metric_values(const IndexStatement *s, const char **why) {
    int none[INDEX_LETTERS] = {0};
    index_lower = arena_alloc(sizeof *index_lower * (size_t)s->dimension);
    index_upper = arena_alloc(sizeof *index_upper * (size_t)s->dimension);
    if (!index_lower || !index_upper) return 0;
    for (int i = 0; i < s->dimension; i++) {
        Rat top = s->metric_top ? index_value(s->metric_top[i], none) : rat_frac(s->metric[i]);
        Rat bottom = s->metric_top ? index_value(s->metric_bottom[i], none) : index_whole(1);
        if (failure || index_stopped) return 0;
        if (!top.num.count || !bottom.num.count) {
            *why = "un elemento della diagonale della metrica, o il suo denominatore, è identicamente zero: la metrica non avrebbe un'inversa";
            return 0;
        }
        /* Gli elementi sono fatti di numeri e di lettere: top e bottom hanno
         * denominatore 1, e il rapporto si scrive senza dividere. */
        index_lower[i] = rat_make(top.num, bottom.num);
        index_upper[i] = rat_make(bottom.num, top.num);
    }
    return 1;
}

/* Aggiunge al testo out, lungo *length e capiente size, un pezzo con la
 * sintassi di printf. Ritorna 0, senza cambiare *length, se non ci sta. */
static int index_append(char *out, size_t size, size_t *length, const char *format, ...) {
    va_list arguments;
    va_start(arguments, format);
    int written = vsnprintf(out + *length, size - *length, format, arguments);
    va_end(arguments);
    if (written < 0 || (size_t)written >= size - *length) return 0;
    *length += (size_t)written;
    return 1;
}

/* Ritorna l'indice di posto i, da 1 a d, della componente di posto place di
 * un tensore con rank indici: la cifra i, dalla più significativa, di place
 * scritto in base d con rank cifre, più uno (vedi index_leaf()). */
static int index_digit(long long place, int rank, int i) {
    for (int k = rank - 1; k > i; k--) place /= index_dimension;
    return (int)(place % index_dimension) + 1;
}

/* 38f. Scrive in out, capiente size, il polinomio p nelle componenti dei
 * tensori, come lo legge il capitolo 37: le componenti con gli indici
 * numerici, a_{12}, e una potenza come prodotto ripetuto, perché in quella
 * notazione le potenze non ci sono. Ritorna 0 se non si può: il testo non
 * ci sta, oppure le dimensioni sono più di nove, e un indice non è più una
 * cifra.
 *
 * Dove stanno gli indici. Senza metrica in basso: lì in alto o in basso è
 * lo stesso. Con una metrica dichiarata un atomo è la componente del
 * tensore con gli indici dove sono dichiarati, cioè dove stanno nella sua
 * prima occorrenza, e così è scritta: A^{1} B_{1}, T^{1}{}_{2}. Scritta in
 * basso, A_{1}, nell'enunciato vorrebbe dire la componente abbassata, che
 * è un altro numero. Gli indici sono scritti a partire dall'origine
 * dell'enunciato (38f). */
static int index_put_poly(char *out, size_t size, Poly p) {
    const IndexStatement *s = index_statement;
    size_t length = 0;
    out[0] = 0;
    if (p.count == 0) return index_append(out, size, &length, "0");
    for (int i = 0; i < p.count; i++) {
        const Term *term = &p.term[i];
        Frac c = term->coef.re;
        int negative = c.num < 0, bare;
        if (term->coef.im.num != 0) return 0;
        if (negative) c = frac_neg(c);

        /* Il segno e il coefficiente; un 1 davanti a delle componenti non si
         * scrive. */
        bare = c.num == 1 && c.den == 1 && term->mono.count > 0;
        if (!index_append(out, size, &length, "%s", i == 0 ? (negative ? "-" : "") : (negative ? " - " : " + "))) return 0;
        if (!bare && !(c.den == 1 ? index_append(out, size, &length, "%lld", c.num) : index_append(out, size, &length, "\\frac{%lld}{%lld}", c.num, c.den))) return 0;

        /* Le componenti, ognuna tante volte quant'è il suo esponente. */
        for (int f = 0; f < term->mono.count; f++) {
            long long code = atoms[term->mono.factor[f].atom].id - INDEX_ATOMS, place = code / INDEX_LETTERS;
            Frac e = term->mono.factor[f].exp;
            int slot = (int)(code % INDEX_LETTERS), rank = index_ranks[slot];
            if (e.den != 1 || e.num < 1 || (rank > 0 && index_dimension + s->origin - 1 > 9)) return 0;
            const unsigned char *upper = s->metric ? s->reference[slot] : NULL;
            for (long long k = 0; k < e.num; k++) {
                if (!index_append(out, size, &length, bare ? "%c" : " %c", index_letter(slot))) return 0;
                bare = 0;

                /* Gli indici, a gruppi di vicini nella stessa posizione, con
                 * le graffe vuote tra un gruppo e l'altro. */
                for (int d = 0; d < rank; d++) {
                    int above = upper && upper[d], opens = d == 0 || above != (upper && upper[d - 1]);
                    if (opens && !index_append(out, size, &length, "%s%s{", d ? "}{}" : "", above ? "^" : "_")) return 0;
                    if (!index_append(out, size, &length, "%d", index_digit(place, rank, d) + s->origin - 1)) return 0;
                }
                if (rank > 0 && !index_append(out, size, &length, "}")) return 0;
            }
        }
    }
    return 1;
}

/* 38f. Rilegge i valori scritti da index_put_poly() per i due membri in un
 * punto, left_text e right_text, e ritorna 1 se, ricalcolati, sono proprio
 * i polinomi left e right. Li legge il capitolo 37, come un'identità senza
 * indici liberi nella dimensione dell'enunciato: così ciò che il verdetto
 * mostra è stato letto da chi legge gli enunciati, e non solo scritto. */
static int index_reread(const char *left_text, const char *right_text, Poly left, Poly right) {
    static char text[2 * MAX_FORMULA];
    IndexStatement again;
    const IndexStatement *current = index_statement;
    int value[INDEX_LETTERS] = {0};
    if (snprintf(text, sizeof text, "%s = %s", left_text, right_text) >= (int)sizeof text) return 0;
    if (!parse_index_values(text, index_dimension, current->origin, &again) || again.free) return 0;

    /* Una lettera deve nominare lo stesso tensore dell'enunciato e, con una
     * metrica, avere gli indici dove l'enunciato li dichiara: è la
     * componente che il polinomio nomina. */
    for (int slot = 0; slot < INDEX_LETTERS; slot++) {
        if (again.rank[slot] < 0) continue;
        if (again.rank[slot] != index_ranks[slot]) return 0;
        if (current->metric && memcmp(index_first[slot]->upper, current->reference[slot], (size_t)again.rank[slot]) != 0) return 0;
    }
    index_prepare(again.left);
    index_prepare(again.right);
    if (failure) return 0;

    /* I valori scritti sono un'identità a sé, senza metrica: nominano le
     * componenti con gli indici numerici, ognuna sempre nelle stesse
     * posizioni, e non alzano né abbassano nulla. */
    index_statement = &again;
    Rat reread = index_value(again.left, value), other = index_value(again.right, value);
    int same = index_plain(reread) && index_plain(other) && poly_equal(reread.num, left) && poly_equal(other.num, right) && !failure && !index_stopped;
    index_statement = current;
    return same;
}

/* Scrive in out, capiente size, il punto value[] degli indici liberi free
 * dell'enunciato s: "i = 1, j = 2", con ogni uguaglianza tra due quote (il
 * dollaro per il LaTeX, niente per il verdetto), gli indici con il nome che
 * hanno nell'enunciato e i valori contati dalla sua origine (38f). Ritorna
 * 0 se non ci sta. */
static int index_put_point(char *out, size_t size, const IndexStatement *s, const int *value, const char *quote) {
    size_t length = 0;
    out[0] = 0;
    for (int slot = 0, first = 1; slot < INDEX_LETTERS; slot++) {
        if (!(s->free >> slot & 1)) continue;
        if (!index_append(out, size, &length, "%s%s%s = %d%s", first ? "" : ", ", quote, s->label[slot], value[slot] + s->origin - 1, quote)) return 0;
        first = 0;
    }
    return 1;
}

/* Il punto d'esempio della dimostrazione scritta: il primo in cui i due
 * membri non sono zero, con il loro valore riletto (38f). index_sampled è 0
 * se un tale punto non c'è o non si è potuto scrivere; il testo del punto è
 * vuoto quando non ci sono indici liberi. */
static char index_sample_point[1024], index_sample_value[512];
static int index_sampled;

/* 38d. Prova tutti i punti degli indici liberi dell'enunciato s, già
 * preparato. Ritorna 1 se in ognuno i due membri sono uguali; 0 se in uno
 * sono diversi, e allora value[] è quel punto e *left e *right i due
 * valori, ancora nell'arena (frazioni di polinomi, 38h); -1 se il conto non è arrivato in fondo
 * (`failure`, o il budget in index_stopped); -2 se in un punto l'identità
 * svolta e quella scritta non hanno gli stessi valori. *points è il numero
 * dei punti provati.
 *
 * Con una metrica dichiarata s->left e s->right sono l'identità svolta
 * (39c in parser.c), che è quella decisa e certificata. Che lo svolgimento
 * non abbia cambiato l'enunciato si ricontrolla qui, in ogni punto: i due
 * membri dell'identità com'è scritta, calcolati con i fattori degli indici
 * spostati (index_leaf()), devono essere gli stessi polinomi. Sono due
 * conti diversi: uno contrae con la metrica su una lettera nuova, l'altro
 * moltiplica per un numero. */
static int index_decide(IndexStatement *s, int *value, long long *points, Rat *left, Rat *right) {
    index_sampled = 0;
    *points = 0;
    for (int slot = 0; slot < INDEX_LETTERS; slot++) value[slot] = 1;
    for (;;) {
        /* Un punto: i due membri, e la loro differenza (capitolo 12). */
        size_t mark = arena_used;
        *left = index_value(s->left, value);
        *right = index_value(s->right, value);
        int equal = index_same(*left, *right);
        if (failure || index_stopped) return -1;
        if (s->metric) {
            Rat written = index_value(s->written_left, value);
            int same = index_same(written, *left) && index_same(index_value(s->written_right, value), *right);
            if (failure || index_stopped) return -1;
            if (!same) return -2;
        }
        ++*points;
        if (!equal) return 0;

        /* Il primo punto con un valore non nullo fa da esempio nella
         * dimostrazione, se il suo valore si scrive e si rilegge. */
        if (!index_sampled && left->num.count && index_plain(*left) && index_put_poly(index_sample_value, sizeof index_sample_value, left->num) &&
            index_reread(index_sample_value, index_sample_value, left->num, left->num))
            index_sampled = index_put_point(index_sample_point, sizeof index_sample_point, s, value, "$");
        if (failure || index_stopped) return -1;

        /* Ogni punto è un conto a sé: l'arena torna com'era. */
        arena_used = mark;

        /* Il punto successivo, come un contachilometri: la prima lettera
         * libera che non è a d sale di uno, quelle prima tornano a 1. */
        int slot = 0;
        for (; slot < INDEX_LETTERS; slot++) {
            if (!(s->free >> slot & 1)) continue;
            if (value[slot] < s->dimension) { value[slot]++; break; }
            value[slot] = 1;
        }
        if (slot == INDEX_LETTERS) return 1;
    }
}

/* 38e. Scrive nel certificato il numero razionale q. */
static void index_cert_number(Frac q) {
    if (q.den == 1) cert_add("%lld", q.num);
    else cert_add("(frac %lld %lld)", q.num, q.den);
}

/* 38e. Scrive nel certificato l'espressione node, nella notazione del
 * capitolo 19 di checker.c: l'operatore davanti e tutte le parentesi. Con
 * una metrica dichiarata node è dell'identità svolta. */
static void index_cert(const IndexNode *node) {
    if (node->kind == IX_NUM) {
        index_cert_number(node->number);
    } else if (node->kind == IX_NEG) {
        cert_add("(neg ");
        index_cert(node->a);
        cert_add(")");
    } else if (index_is_leaf(node)) {
        /* \varepsilon con una metrica: il valore dichiarato, per il simbolo. */
        int scaled = node->kind == IX_EPSILON && index_statement->metric && (index_statement->epsilon.num != 1 || index_statement->epsilon.den != 1);
        if (scaled) {
            cert_add("(* ");
            index_cert_number(index_statement->epsilon);
            cert_add(" ");
        }
        if (node->kind == IX_TENSOR) cert_add("(t %c", node->name);
        else cert_add(node->kind == IX_DELTA ? "(delta" : node->kind == IX_EPSILON ? "(eps" : node->kind == IX_LOWER ? "(metric" : "(inverse");
        for (int i = 0; i < node->rank; i++) cert_add(node->index[i] < 'A' ? " %d" : " %c", node->index[i]);
        cert_add(scaled ? "))" : ")");
    } else {
        cert_add(node->kind == IX_ADD ? "(+ " : node->kind == IX_SUB ? "(- " : "(* ");
        index_cert(node->a);
        cert_add(" ");
        index_cert(node->b);
        cert_add(")");
    }
}

/* 38e. Scrive nel certificato il polinomio p nelle componenti dei tensori,
 * nella stessa notazione: una somma di termini, ognuno il coefficiente per
 * le sue componenti con gli indici numerici. */
static void index_cert_poly(Poly p) {
    if (p.count == 0) cert_add("0");
    for (int i = 0; i < p.count; i++) {
        const Term *term = &p.term[i];
        long long copies = 0;
        if (term->coef.im.num != 0) certificate_broken = 1;
        for (int f = 0; f < term->mono.count; f++) {
            if (term->mono.factor[f].exp.den != 1 || term->mono.factor[f].exp.num < 1) certificate_broken = 1;
            copies += term->mono.factor[f].exp.num;
        }
        if (certificate_broken) return;

        /* (+ T1 (+ T2 T3)), e ogni termine (* (* c X) Y). */
        if (i + 1 < p.count) cert_add("(+ ");
        for (long long k = 0; k < copies; k++) cert_add("(* ");
        index_cert_number(term->coef.re);
        for (int f = 0; f < term->mono.count; f++) {
            long long code = atoms[term->mono.factor[f].atom].id - INDEX_ATOMS, place = code / INDEX_LETTERS;
            int slot = (int)(code % INDEX_LETTERS), rank = index_ranks[slot];
            for (long long k = 0; k < term->mono.factor[f].exp.num; k++) {
                cert_add(" (t %c", index_letter(slot));
                for (int d = 0; d < rank; d++) cert_add(" %d", index_digit(place, rank, d));
                cert_add("))");
            }
        }
        if (i + 1 < p.count) cert_add(" ");
    }
    for (int i = 1; i < p.count; i++) cert_add(")");
}

/* Scrive nella dimostrazione il numero razionale q, in LaTeX. */
static void index_put_number(Frac q) {
    if (q.den == 1) proof_add("%lld", q.num);
    else proof_add("%s\\frac{%lld}{%lld}", q.num < 0 ? "-" : "", q.num < 0 ? -q.num : q.num, q.den);
}

/* Ritorna quanti sono gli elementi del tensore dato di posto slot
 * nell'enunciato s: d elevato al suo rango, che è 1 o 2 (39d in parser.c). */
static int index_given_count(const IndexStatement *s, int slot) {
    return s->rank[slot] == 2 ? s->dimension * s->dimension : s->dimension;
}

/* Ritorna quanti sono i tensori di s dati per componenti (given diverso da
 * zero) oppure qualsiasi (given zero); se write non è zero ne scrive anche
 * le lettere nella dimostrazione, separate da virgole. */
static int index_letters(const IndexStatement *s, int given, int write) {
    int count = 0;
    for (int slot = 0; slot < INDEX_LETTERS; slot++) {
        if (s->rank[slot] < 0 || (s->given[slot] != NULL) != (given != 0)) continue;
        if (write) proof_add(count ? ", $%c$" : " $%c$", index_letter(slot));
        count++;
    }
    return count;
}

/* Scrive nella dimostrazione le convenzioni con cui l'enunciato s è stato
 * letto (37a-37d, e 39a-39e con le ipotesi): la dimensione, la metrica, i
 * valori degli indici, gli indici ripetuti, i simboli che compaiono, i
 * tensori dati per componenti, i tensori qualsiasi. */
static void index_put_conventions(const IndexStatement *s, int has_delta, int has_epsilon) {
    int first = s->origin, last = s->origin + s->dimension - 1;
    if (s->metric) {
        proof_add("The statement is read in dimension $%d$ with the declared metric, which is diagonal: $g_{ii} = ", s->dimension);
        for (int i = 0; i < s->dimension; i++) {
            /* 38h. Un elemento che è una funzione: numeratore e denominatore
             * di g_{ii}, se sono polinomi che si sanno scrivere. */
            static char above[256], below[256];
            proof_add(i ? ", " : "");
            if (!s->metric_top) index_put_number(s->metric[i]);
            else if (index_plain(index_lower[i]) && index_put_poly(above, sizeof above, index_lower[i].num)) proof_add("%s", above);
            else if (index_plain(index_upper[i]) && index_put_poly(below, sizeof below, index_upper[i].num)) proof_add("\\frac{1}{%s}", below);
            else proof_add("\\ast");
        }
        proof_add("$ for $i = %d, \\dots, %d$, and $g^{ii} = 1/g_{ii}$. Every index takes the values from $%d$ to $%d$, and an index written once "
                  "above and once below in a product is summed over them (Einstein convention). A tensor has its indices in the positions where "
                  "the statement first writes it; an index written in the other position has been raised or lowered with the metric. ",
                  first, last, first, last);
        if (s->metric_top) proof_add("The letters in the entries of the metric are the coordinates and the parameters: the identity is proved where "
                                     "every entry of the metric is defined and different from zero. ");
        if (has_delta) proof_add("The symbol $\\delta^{i}_{j}$ is $1$ when $i = j$ and $0$ otherwise. ");
        if (has_epsilon) {
            proof_add("The symbol $\\varepsilon$ with its $%d$ indices %s is $", s->dimension, s->epsilon_upper ? "above" : "below");
            index_put_number(s->epsilon);
            proof_add("$ times the sign of the permutation they form, and $0$ when two of them coincide. ");
        }
    } else {
        proof_add("The statement is read in dimension $%d$: every index takes the values from $%d$ to $%d$, and an index written twice in a product "
                  "is summed over them (Einstein convention); upper and lower indices are not distinguished. ", s->dimension, first, last);
        if (has_delta) proof_add("The symbol $\\delta_{ij}$ is $1$ when $i = j$ and $0$ otherwise. ");
        if (has_epsilon) proof_add("The symbol $\\varepsilon$ with $%d$ indices is the sign of the permutation they form, and $0$ when two of them coincide. ", s->dimension);
    }

    /* 38g. I tensori dati, poi quelli che restano qualsiasi. */
    int tensors = index_letters(s, 1, 0);
    if (tensors) {
        proof_add(tensors == 1 ? "The components of" : "The components of each of");
        index_letters(s, 1, 1);
        proof_add(" are the ones that the statement declares, with the indices in the positions written there: in a table the first index is the row "
                  "and the second the column, and the first row and column are the value $%d$. ", first);
    }
    tensors = index_letters(s, 0, 0);
    if (!tensors) return;
    proof_add(tensors == 1 ? "The letter" : "The letters");
    index_letters(s, 0, 1);
    proof_add(tensors == 1 ? " denotes an arbitrary tensor: its" : " denote arbitrary tensors: their");
    proof_add(" components are independent unknowns, and the two sides are compared as polynomials in them. ");
}

/* Ritorna 1 se nel sottoalbero node compare un simbolo di tipo kind. */
static int index_mentions(const IndexNode *node, IndexKind kind) {
    if (!node) return 0;
    return node->kind == kind || index_mentions(node->a, kind) || index_mentions(node->b, kind);
}

/* Decide l'identità con gli indici scritta in formula (capitolo 37) e ne
 * ritorna il verdetto: DIMOSTRATO o FALSO, con il certificato che il
 * verificatore ha accettato e la dimostrazione o il controesempio scritti,
 * oppure perché non si è potuto.
 *
 * Svuota l'arena e la tabella degli atomi: i risultati di chiamate
 * precedenti non sono più validi. */
static Verdict prove_indices(const char *formula) {
    static char note[640], detail[1024 + 2 * 512 + 96], point[1024], side[2][512];
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, "con il conto su tutti i valori degli indici", NULL, NULL};
    IndexStatement statement;
    int value[INDEX_LETTERS];
    long long points;
    Rat left, right;

    /* Ripartenza da zero per il nuovo enunciato, e lettura. */
    proof_reset();
    arena_used = arena_keep;
    atom_count = 0;
    base_poly_count = 0;
    failure = NULL;
    /* Con delle ipotesi davanti a \implies l'enunciato dichiara una
     * metrica, delle componenti o i valori degli indici (capitolo 39 di
     * parser.c); senza, è del capitolo 37. */
    int read = strstr(formula, "\\implies") ? parse_index_hypotheses(formula, &statement) : parse_index_statement(formula, &statement);
    if (!read) { verdict.reason = syntax_error ? syntax_error : failure; return verdict; }
    const IndexNode *shown[2] = {statement.metric ? statement.written_left : statement.left, statement.metric ? statement.written_right : statement.right};
    int has_delta = index_mentions(shown[0], IX_DELTA) || index_mentions(shown[1], IX_DELTA);
    int has_epsilon = index_mentions(shown[0], IX_EPSILON) || index_mentions(shown[1], IX_EPSILON);
    int has_given = index_letters(&statement, 1, 0) > 0, has_tensors = index_letters(&statement, 0, 0) > 0;
    /* Con una metrica la nota dice anche di che cosa è il certificato: il
     * verificatore ricontrolla l'identità svolta (39c), e che sia la stessa
     * di quella scritta lo ricontrolla solo il motore (index_decide()). */
    snprintf(note, sizeof note, "in dimensione %d%s: gli indici vanno da %d a %d, sono sommati se ripetuti, %s%s%s%s%s", statement.dimension,
             statement.metric ? ", con la metrica dichiarata" : "", statement.origin, statement.origin + statement.dimension - 1,
             statement.metric ? "uno in alto e uno in basso" : "e in alto o in basso sono lo stesso",
             has_given ? "; i tensori dati hanno le componenti dichiarate" : "",
             !has_tensors ? "" : has_given ? "; le altre lettere sono tensori qualsiasi" : "; le lettere sono tensori qualsiasi",
             statement.metric ? "; il certificato è dell'identità svolta, dove alzare e abbassare un indice è una contrazione con la metrica" : "",
             statement.metric_top ? "; vale dove gli elementi della metrica sono definiti e diversi da zero" : "");

    /* 38b-38d. Il conto. */
    index_dimension = statement.dimension;
    index_ranks = statement.rank;
    index_statement = &statement;
    index_work = 0;
    index_stopped = 0;
    index_prepare(statement.left);
    index_prepare(statement.right);
    if (statement.metric) {
        index_prepare(statement.written_left);
        index_prepare(statement.written_right);
    }
    for (int slot = 0; slot < INDEX_LETTERS; slot++)
        for (int k = 0; statement.given[slot] && k < index_given_count(&statement, slot); k++) index_prepare(statement.given[slot][k]);
    /* 38h. Gli elementi della metrica e i loro inversi. */
    for (int i = 0; statement.metric_top && i < statement.dimension; i++) {
        index_prepare(statement.metric_top[i]);
        index_prepare(statement.metric_bottom[i]);
    }
    const char *singular = NULL;
    if (statement.metric && !failure && !index_metric_values(&statement, &singular) && singular) {
        verdict.reason = singular;
        return verdict;
    }
    int outcome = failure || index_stopped ? -1 : index_decide(&statement, value, &points, &left, &right);
    if (outcome == -2) {
        /* Lo svolgimento ha cambiato l'enunciato: un errore del lettore. */
        unjustified_steps++;
        verdict.outcome = NOT_PROVED;
        verdict.reason = "lo svolgimento degli indici alzati e abbassati non è confermato dal conto sull'identità com'è scritta";
        return verdict;
    }
    if (outcome < 0) {
        verdict.outcome = NOT_PROVED;
        verdict.reason = failure ? failure : "il conto su tutti i valori degli indici è troppo lungo per il budget di lavoro (--model-steps)";
        return verdict;
    }

    /* 38f. I valori dei due membri nel controesempio, se si scrivono e,
     * riletti, sono quelli. Uno scritto che non si rilegge è un errore di
     * chi scrive, e il verdetto non viene emesso. */
    int written = 0, plain = !outcome && index_plain(left) && index_plain(right);
    if (plain) {
        written = index_put_poly(side[0], sizeof side[0], left.num) && index_put_poly(side[1], sizeof side[1], right.num);
        if (written && !index_reread(side[0], side[1], left.num, right.num)) {
            unjustified_steps++;
            verdict.outcome = NOT_PROVED;
            verdict.reason = "i valori scritti dei due membri nel controesempio, riletti, non sono confermati";
            return verdict;
        }
    }

    /* 38e. Il certificato: l'enunciato, la dimensione, e ciò che il conto ha
     * stabilito. */
    certificate_length = 0;
    certificate_broken = 0;
    cert_add("certificate indices\ndimension %d\n", statement.dimension);
    if (statement.metric) {
        /* 38h. Un elemento che è una funzione va con il suo numeratore e il
         * suo denominatore: (/ N D). */
        cert_add("metric");
        for (int i = 0; i < statement.dimension; i++) {
            cert_add(" ");
            if (!statement.metric_top) { index_cert_number(statement.metric[i]); continue; }
            cert_add("(/ ");
            index_cert(statement.metric_top[i]);
            cert_add(" ");
            index_cert(statement.metric_bottom[i]);
            cert_add(")");
        }
        cert_add("\n");
    }
    /* 38g. Le componenti date: il nome, il rango, e gli elementi per righe. */
    for (int slot = 0; slot < INDEX_LETTERS; slot++) {
        if (!statement.given[slot]) continue;
        cert_add("given %c %d", index_letter(slot), statement.rank[slot]);
        for (int k = 0; k < index_given_count(&statement, slot); k++) {
            cert_add(" ");
            index_cert(statement.given[slot][k]);
        }
        cert_add("\n");
    }
    cert_add("statement (= ");
    index_cert(statement.left);
    cert_add(" ");
    index_cert(statement.right);
    cert_add(")\n");
    if (outcome) {
        cert_add("holds\n");
    } else {
        cert_add("fails");
        for (int slot = 0; slot < INDEX_LETTERS; slot++)
            if (statement.free >> slot & 1) cert_add(" %c %d", index_letter(slot), value[slot]);
        /* I valori dei due membri, quando sono polinomi (38h). */
        if (plain) {
            cert_add("\nleft ");
            index_cert_poly(left.num);
            cert_add("\nright ");
            index_cert_poly(right.num);
        }
        cert_add("\n");
    }
    cert_add("end\n");
    const char *text = certificate_text, *why = "il certificato non si è potuto scrivere";
    CkAnswer answer = certificate_broken ? CK_UNSUPPORTED : ck_check(&text, &why, checker_steps());
    if (answer != CK_ACCEPTED) {
        /* Respinto: i due conti non sono d'accordo, e uno dei due sbaglia.
         * Non controllabile: manca la verifica indipendente. In nessuno dei
         * due casi c'è un risultato. */
        if (answer == CK_REJECTED) unjustified_steps++;
        snprintf(certificate_problem, sizeof certificate_problem, "il verificatore indipendente %s: %s",
                 answer == CK_REJECTED ? "ha respinto il certificato" : "non sa controllare il certificato", why);
        verdict.outcome = NOT_PROVED;
        verdict.reason = certificate_problem;
        return verdict;
    }
    verdict.certificate = certificate_text;
    verdict.note = note;

    /* La dimostrazione scritta: le convenzioni, i casi provati, un esempio. */
    if (outcome) {
        proof_add("\\textbf{Proof.} ");
        index_put_conventions(&statement, has_delta, has_epsilon);
        if (statement.free) {
            int single = !(statement.free & (statement.free - 1));
            proof_add(single ? "The free index is " : "The free indices are ");
            for (int slot = 0, first = 1; slot < INDEX_LETTERS; slot++)
                if (statement.free >> slot & 1) { proof_add(first ? "$%s$" : ", $%s$", statement.label[slot]); first = 0; }
            proof_add(": there are $%lld$ choices of %s, and for each one the two sides were computed and coincide. ", points,
                      single ? "its value" : "their values");
            if (index_sampled) proof_add("For example, for %s both sides are $%s$. ", index_sample_point, index_sample_value);
        } else {
            proof_add("There are no free indices: the two sides were computed and coincide. ");
            if (index_sampled) proof_add("Their common value is $%s$. ", index_sample_value);
        }
        proof_add("$\\Box$");
        verdict.outcome = PROVED;
        verdict.proof = proof_text;
        return verdict;
    }

    /* Il controesempio: il punto, e i due valori se si sono potuti scrivere. */
    if (!statement.free || !index_put_point(point, sizeof point, &statement, value, "")) snprintf(point, sizeof point, "senza indici liberi");
    if (written) snprintf(detail, sizeof detail, "%s: il primo membro vale %s, il secondo %s", point, side[0], side[1]);
    else snprintf(detail, sizeof detail, "%s: i due membri sono diversi", point);
    proof_add("\\textbf{Counterexample.} ");
    index_put_conventions(&statement, has_delta, has_epsilon);
    if (statement.free && index_put_point(point, sizeof point, &statement, value, "$")) proof_add("For %s the ", point);
    else proof_add("The ");
    if (written) proof_add("left-hand side is $%s$ and the right-hand side is $%s$", side[0], side[1]);
    else proof_add("two sides are different");
    proof_add(has_tensors ? ": two different polynomials in the components, which take different values for some choice of the tensors." : ".");
    verdict.outcome = REFUTED;
    verdict.detail = detail;
    verdict.proof = proof_text;
    return verdict;
}

/* Ritorna 1 se formula è un'identità con gli indici, cioè un enunciato di
 * questo capitolo: contiene una delta di Kronecker o un simbolo di
 * Levi-Civita con i suoi indici, \delta o \varepsilon o \epsilon seguiti da
 * _ o da ^, e non dichiara nulla con \colon.
 *
 * Perché proprio questo. Nessun altro linguaggio del programma legge quei
 * simboli con un indice, tranne quello degli insiemi qualsiasi, dove
 * \delta_{1} può essere il nome di un'applicazione: ma lì va dichiarata, con
 * \colon. Così nessun enunciato che prima era letto cambia significato.
 * Un'identità con le sole componenti, senza delta né simbolo di
 * Levi-Civita, non è riconosciuta dalla forma: a_{i} b_{i} si scrive come
 * un termine di una successione del capitolo 13, e non c'è modo di
 * distinguerli. La riconosce una metrica dichiarata tra le ipotesi, con
 * \operatorname{diag} (capitolo 39 di parser.c): chi la dichiara parla di
 * tensori.
 *
 * Un enunciato che comincia con il segno di derivata o con \lim resta al suo
 * capitolo: lì una \varepsilon è una variabile che quel lettore non conosce,
 * e il motivo del rifiuto deve restare il suo.
 *
 * Usa il lettore di token del parser, e lascia il suo stato da reimpostare. */
static int uses_index_notation(const char *formula) {
    int found = 0;
    if (strstr(formula, "\\colon") || starts_with_derivative(formula) || starts_with_limit(formula)) return 0;
    syntax_error = NULL;
    cursor = formula;
    for (next_token(); token.kind != T_END && !found; ) {
        int symbol = is_command("delta") || is_command("varepsilon") || is_command("epsilon");
        next_token();
        found = symbol && (is_char('_') || is_char('^'));
    }
    syntax_error = NULL;
    return found || strstr(formula, "{diag}") != NULL;
}

