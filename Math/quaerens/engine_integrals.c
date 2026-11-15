/* =============================================================================
 * 30. INTEGRALI: PRIMITIVE, INTEGRALI DEFINITI E IMPROPRI
 * ============================================================================
 *
 * A che cosa serve. Le domande dei libri sugli integrali, nella notazione
 * del paragrafo 9j di parser.c:
 *
 *     \int f \, dx = F + c        è giusta questa primitiva?
 *     \int f \, dx                trovane una (la risposta è RISOLTO: F + c);
 *     \int_{a}^{b} f \, dx = V    è giusto questo valore? Senza "= V": quanto vale?
 *     \int_{1}^{+\infty} f \, dx = +\infty, \in \mathbb{R}, \notin \mathbb{R}
 *                                 un integrale improprio diverge? converge?
 *
 * VERIFICARE UNA PRIMITIVA (30a, 30b)
 *
 * Una primitiva di f su un intervallo aperto I è una funzione F derivabile in
 * I con F' = f. Due primitive sullo stesso intervallo differiscono per una
 * costante: se F' = G' in I la derivata di G - F è zero, e per il teorema di
 * Lagrange G - F è costante su I. Quindi "\int f \, dx = F + c" dice che su
 * ogni intervallo aperto in cui F e f sono definite le primitive di f sono
 * le F + c, ed è vero se e solo se lì F' = f. Su intervalli diversi la
 * costante può cambiare (1/x ha ln|x| + c_1 per x < 0 e ln|x| + c_2 per
 * x > 0): i libri le chiamano tutte c, e qui non si confrontano le F scritte
 * ma solo le loro derivate.
 *
 * È il controllo del capitolo 27 ribaltato. derive() calcola F' con le
 * regole di derivazione (27c-27g) e il test di annullamento (capitolo 12)
 * decide se F' - f è zero, con i conti esatti, dove i due membri sono
 * definiti: lì può usare i fatti del dominio (12d), come x >= 0 quando
 * compare \sqrt{x}; poi, per una strada che non
 * usa quelle regole, la serie di Taylor di F nei punti di prova, calcolata
 * con gli intervalli (27h), dà F'(x0) con l'errore garantito e la si
 * confronta con f(x0). DIMOSTRATO vuole lo zero esatto e almeno un punto in
 * cui i numeri confermano; FALSO vuole un punto x0 in cui F e f sono
 * definite e F'(x0) è di sicuro diverso da f(x0), sia per la serie di
 * Taylor sia per le regole, che lì devono concordare tra loro. Una regola
 * smentita dalla serie è un errore del programma (unjustified_steps).
 *
 * TROVARE UNA PRIMITIVA (30c-30h)
 *
 * La ricerca può essere euristica, il verdetto no: ogni primitiva trovata
 * viene scritta in LaTeX, riletta dal lettore del programma come se l'avesse
 * scritta l'utente, e verificata come sopra. I metodi sono quelli generali
 * dei libri, ognuno con il suo teorema scritto dove è il codice:
 *
 *   30c. la linearità, e l'ordine in cui si provano i metodi;
 *   30d. le funzioni razionali, per intero: divisione, Hermite-Ostrogradsky
 *        per i fattori ripetuti, fattori del denominatore su Q (radici
 *        razionali e fattori di secondo grado), fratti semplici con un
 *        sistema lineare esatto, logaritmi e arcotangenti; e x^m = s quando
 *        la funzione è x^{m-1} R(x^m);
 *   30e. i polinomi per esponenziali, P(x) e^{(a + i b) x}: seni e coseni
 *        sono esponenziali complessi (capitolo 11), quindi le potenze di
 *        seni e coseni, i loro prodotti (Werner), x^n sin x, e^x sin x (il
 *        caso "ciclico" dell'integrazione per parti) sono un caso solo;
 *   30f. per parti, con la regola di scelta: si deriva il logaritmo o
 *        l'arcotangente, si integra il resto;
 *   30g. per sostituzione: t = h(x) quando la funzione è g(h(x)) h'(x), a
 *        meno di una costante; e le sostituzioni che rendono la funzione
 *        razionale, t = (a x + b)^{1/n} e t = b^{g x};
 *   30h. le funzioni razionali di seno e coseno, con t = tan(x/2), o
 *        t = tan x quando la funzione non cambia sommando pi a x.
 *
 * GLI INTEGRALI DEFINITI (30i, 30j)
 *
 * Teorema fondamentale del calcolo integrale: se f è continua su [a, b] e F
 * è derivabile in un intervallo aperto che contiene [a, b] con F' = f, allora
 * l'integrale di f da a a b vale F(b) - F(a). Le ipotesi si controllano con
 * gli intervalli del capitolo 24, su una suddivisione di [a, b] (vedi 30i);
 * F(b) - F(a) si calcola con i conti esatti, con i valori esatti di seni,
 * coseni e arcotangenti negli angoli multipli di pi/12 (30i-1), e si
 * confronta con il valore scritto con il test di annullamento. Un valore
 * assoluto si toglie dividendo [a, b] nei punti in cui il suo argomento si
 * annulla (30i-2). Il controllo indipendente è una somma di Riemann con gli
 * intervalli, che chiude il valore vero tra due numeri senza usare F: il
 * valore esatto deve starci dentro. La stessa somma basta per dire FALSO,
 * quando il valore scritto ne sta di sicuro fuori.
 *
 * GLI INTEGRALI IMPROPRI (30k, 30l)
 *
 * Un estremo infinito, o una funzione non limitata vicino a un estremo o a
 * un punto interno: l'integrale è un limite di integrali su intervalli
 * compatti. Con una primitiva F (30k) è il limite di F agli estremi, che
 * calcola il capitolo 29 con la scala delle crescite (29k), dopo che la
 * tabella dei segni ha mostrato le funzioni definite sull'intervallo aperto
 * e diviso l'intervallo nei punti in cui non lo sono. Senza primitiva (30l)
 * la convergenza si decide per confronto con t^{e} (\ln\frac{1}{t})^{d}, dal
 * termine principale della funzione (29m). Anche un integrale definito che
 * 30i non vede continuo su [a, b], come \sqrt[5]{x} su [-1, 0], passa da qui.
 *
 * IL CERTIFICATO (30cert)
 *
 * Una primitiva verificata, o trovata, e un integrale definito portano un
 * certificato per checker.c (capitolo 13), scritto con le funzioni di 27m:
 * il verificatore deriva la primitiva da sé e controlla che la sua derivata
 * sia la funzione integranda; per un integrale anche che la funzione e la
 * primitiva siano definite su tutto [a, b], con Sturm, e che il valore sia
 * F(b) - F(a). Un rifiuto rende il verdetto NON DIMOSTRATO. Gli integrali
 * impropri (30k, 30l) restano senza certificato: il verificatore non sa
 * calcolare limiti di primitive.
 *
 * COSA NON C'È ANCORA
 *
 *   - Le aree, e negli integrali impropri le oscillazioni
 *     (\int_0^{+\infty} \cos x \, dx non converge, ma il motore non lo sa
 *     dire), i domini che la tabella dei segni non sa decidere
 *     (\frac{1}{e^{\sqrt{x}} - 1} su (0, 1)), le funzioni la cui primitiva non
 *     si trova e la cui convergenza vuole stime più fini del termine
 *     principale.
 *   - Le funzioni che derive() non tratta ancora: il valore assoluto fuori
 *     da un logaritmo (in una primitiva; in un integrale definito lo toglie
 *     30i-2), arcoseno e arcocoseno, seno e coseno iperbolici. Le primitive
 *     che le contengono restano non decise; il lettore e le regole di
 *     derivazione sono del capitolo 27.
 *   - Le radici di polinomi di secondo grado, \sqrt{a x^2 + b x + c}: le
 *     sostituzioni di Eulero e quelle iperboliche. Si verificano le primitive
 *     scritte, ma non si cercano; né si cerca quella di x^3 \sqrt{2 - x^2},
 *     che chiederebbe t = \sqrt{2 - x^2} con x^2 = 2 - t^2.
 *   - ln(e) = 1 nei conti esatti: un estremo come e^{3/2} non si calcola.
 *   - Lettere oltre alla variabile, a e pi greco (i parametri).
 *   - Il certificato (30cert, con le funzioni di 27m) di un integrale diviso
 *     in parti da un valore assoluto (30i-2), e di uno con una condizione di
 *     esistenza che non è un polinomio in x (una tangente, un denominatore
 *     con e^x), o con un estremo diverso da c_0 + c_1 pi + c_2 e: checker.c
 *     li dice non controllabili, e il verdetto dice perché il certificato
 *     manca.
 */

/* 30a. Ritorna una copia di tree in cui ogni logaritmo di un valore assoluto,
 * ln|u| o log_b|u|, è il logaritmo di u: è l'albero da dare a derive(), che
 * il valore assoluto non lo deriva.
 *
 * Perché si può. Dove u > 0 si ha |u| = u, e le due funzioni coincidono.
 * Dove u < 0 si ha ln|u| = ln(-u), con derivata (-u')/(-u) = u'/u: la stessa
 * formula che le regole danno per ln u. Quindi ln|u| e ln u hanno la stessa
 * derivata, u'/u, in ogni punto in cui ln|u| è derivabile: differiscono in
 * dove sono definite, non in come si derivano. Dove F è definita lo decidono
 * qui i conti con i numeri sull'albero com'è scritto (30b), mai questa
 * copia.
 *
 * Lo stesso vale per un valore assoluto che è un fattore dell'argomento,
 * come in \ln\frac{\sqrt{x^2 + 1}}{|x|}: la derivata di ln|g| è g'/g, e per
 * g = A |B|^k / C la derivata logaritmica g'/g = A'/A + k B'/B - C'/C non
 * cambia togliendo il valore assoluto, perché |B|'/|B| = B'/B dove B non è
 * zero. Per questo strip_factor_abs() toglie i valori assoluti che
 * dall'argomento si raggiungono scendendo per prodotti, quozienti, segni e
 * potenze, e solo quelli. */
static Node *strip_log_abs(const Node *tree);
static Node *strip_factor_abs(const Node *tree) {
    if (tree->kind == N_CALL && tree->op == FN_ABS) return strip_factor_abs(tree->a);
    if (tree->kind == N_MUL || tree->kind == N_DIV) return node_new(tree->kind, strip_factor_abs(tree->a), strip_factor_abs(tree->b));
    if (tree->kind == N_NEG) return node_new(N_NEG, strip_factor_abs(tree->a), NULL);
    if (tree->kind == N_POW && tree->b->kind == N_NUM) return node_new(N_POW, strip_factor_abs(tree->a), tree->b);
    return strip_log_abs(tree);
}

static Node *strip_log_abs(const Node *tree) {
    if (!tree) return NULL;
    if (tree->kind == N_CALL && (tree->op == FN_LN || tree->op == FN_LOG)) return node_call((Function)tree->op, strip_factor_abs(tree->a), tree->b);
    Node *copy = node_new(tree->kind, strip_log_abs(tree->a), strip_log_abs(tree->b));
    copy->value = tree->value;
    copy->name = tree->name;
    copy->op = tree->op;
    copy->c = strip_log_abs(tree->c);
    return copy;
}

/* I punti in cui le primitive vengono controllate con i numeri (30b). Sono
 * sparsi perché le funzioni degli esercizi hanno domini diversi: x > 0,
 * x > ln 2, x >= 4, -2 < x < 2, x diverso da 0. */
static const Frac primitive_points[] = {{3, 10}, {7, 5}, {-9, 10}, {5, 2}, {-13, 5}, {9, 2}, {1, 7}, {-1, 3}, {11, 3}, {6, 1}, {-6, 1}, {17, 10}};
enum { PRIMITIVE_POINTS = sizeof primitive_points / sizeof *primitive_points };

/* L'esito della verifica di una primitiva F di f (30a e 30b). */
typedef struct {
    Outcome outcome;     /* PROVED, REFUTED, NOT_PROVED oppure UNSUPPORTED */
    const char *reason;  /* NOT_PROVED, UNSUPPORTED: perché, in italiano */
    Frac point;          /* REFUTED: il punto x0 in cui F'(x0) è di sicuro diverso
                            da f(x0); PROVED: il primo punto in cui i numeri confermano */
    int outside;         /* 1 se in un punto di prova f è definita e F no */
    Frac where;          /* quel punto, se outside */
    Node *derivative;    /* F' secondo le regole di derivazione; NULL se non si calcola */
} PrimitiveCheck;

/* 30a, 30b. Verifica che F sia una primitiva di f nella variabile x: vedi la
 * testa del capitolo. Gli alberi non devono contenere altre lettere che x, e
 * e pi greco. Lascia `failure` a NULL. */
static PrimitiveCheck primitive_check(const Node *f, const Node *F, int x) {
    PrimitiveCheck check = {NOT_PROVED, NULL, {0, 1}, 0, {0, 1}, NULL};

    /* 30a. F' con le regole, e F' - f con i conti esatti, dove i due membri
     * sono definiti (12d): è lì che F' = f deve valere. */
    Node *derivative = derive(strip_log_abs(F), x);
    if (failure) { check.outcome = UNSUPPORTED; check.reason = failure; failure = NULL; return check; }
    check.derivative = derivative;
    Statement claim = {derivative, (Node *)f, REL_EQ};
    int vanishes = vanishes_where_defined(&claim, F, rat_int(0));
    const char *trouble = failure;
    failure = NULL;

    /* 30b. In ogni punto di prova in cui f è definita: la derivata letta
     * dalla serie di Taylor di F, quella delle regole, e f. */
    Node *primitive = sample_tree(F, x, 0, 0), *rules = sample_tree(derivative, x, 0, 0), *integrand = sample_tree(f, x, 0, 0);
    int confirmed = 0, doubt = 0;
    for (int p = 0; p < PRIMITIVE_POINTS && !failure; p++) {
        Range at = range_ratio(primitive_points[p].num, primitive_points[p].den);
        Range value = sample_value(integrand, x, at);
        if (!range_known(value)) continue;
        Jet series = jet_eval(primitive, x, at, 1);
        if (!range_known(series.c[0])) {
            if (!check.outside) { check.outside = 1; check.where = primitive_points[p]; }
            continue;
        }
        Range by_rules = sample_value(rules, x, at);
        int agreement = numbers_agree(by_rules, series.c[1]);
        if (agreement < 0) {
            unjustified_steps++;
            check.reason = "la derivata calcolata con le regole di derivazione è smentita dalla serie di Taylor della primitiva";
            return check;
        }
        if (agreement == 0) continue;

        /* Le regole e la serie concordano: in questo punto si può dire FALSO
         * se f ne è di sicuro lontana per tutti e due i conti. */
        int side, by_series_differs = range_side(range_sub(series.c[1], value), &side);
        int by_rules_differs = range_side(range_sub(by_rules, value), &side);
        if (by_series_differs && by_rules_differs) {
            if (vanishes) {
                unjustified_steps++;
                check.reason = "il test di annullamento dice F' = f, ma i numeri dicono di no";
                return check;
            }
            check.outcome = REFUTED;
            check.point = primitive_points[p];
            return check;
        }
        if (by_series_differs || by_rules_differs) doubt = 1;
        else if (numbers_agree(series.c[1], value) > 0) {
            if (!confirmed) check.point = primitive_points[p];
            confirmed = 1;
        }
    }
    failure = NULL;
    if (!vanishes) check.reason = trouble ? trouble : "la derivata della primitiva, calcolata con le regole, non si riduce alla funzione integranda";
    else if (doubt) check.reason = "in un punto di prova la derivata della primitiva e la funzione integranda non concordano abbastanza per decidere";
    else if (!confirmed) check.reason = "non riesco a confermare con i numeri la derivata della primitiva, in nessuno dei punti di prova";
    else check.outcome = PROVED;
    return check;
}

/* 30c. LA RICERCA DI UNA PRIMITIVA
 *
 * Ogni metodo dei paragrafi seguenti riceve l'albero di f nella variabile x
 * e scrive in un testo una primitiva, in LaTeX; ritorna 0 se non si applica
 * o non riesce. La ricerca li prova in un ordine fisso, dal più completo al
 * più specifico (vedi primitive_methods[] e primitive_text()):
 *
 *   30c-1. f non contiene x: F = f x;
 *   30d.   funzioni razionali, che hanno sempre una primitiva elementare e
 *          un algoritmo completo per trovarla;
 *   30e.   polinomi per esponenziali, anche questi con una formula
 *          generale;
 *   30c-2. linearità: un fattore costante, o un segno, si porta fuori;
 *   30f.   per parti, con un logaritmo o un'arcotangente;
 *   30g.   per sostituzione, e le sostituzioni che rendono la funzione
 *          razionale (una radice, un esponenziale);
 *   30h.   seni e coseni con t = tan(theta/2);
 *   30c-8. linearità: una somma si integra un termine alla volta.
 *
 * Un metodo può chiamare la ricerca su un'altra funzione (per parti la
 * derivata del logaritmo per la primitiva del resto, per sostituzione la
 * funzione nella nuova variabile): la profondità è limitata da
 * MAX_PRIMITIVE_DEPTH, così la ricerca finisce sempre.
 *
 * Perché il risultato è un testo. È ciò che si consegna, e ciò che si
 * verifica: la primitiva trovata viene riletta dal parser del capitolo 9, e
 * un errore nel modo di scriverla (un segno, una parentesi) cambia ciò che si
 * rilegge e non passa la verifica. */

/* Il metodo che ha trovato l'ultima primitiva, per il verdetto. */
static const char *primitive_method;

/* Aggiunge a text, di size byte, il razionale v in LaTeX: 3, -\frac{5}{2}. */
static void frac_latex(Frac v, char *text, size_t size) {
    if (v.den == 1) text_add(text, size, "%lld", v.num);
    else text_add(text, size, "%s\\frac{%lld}{%lld}", v.num < 0 ? "-" : "", v.num < 0 ? -v.num : v.num, v.den);
}

/* Aggiunge alla somma scritta in text il termine coef body: col segno davanti
 * se non è il primo, senza il coefficiente se vale 1 o -1. Un body vuoto è
 * il numero coef; un coefficiente nullo non scrive nulla. */
static void term_latex(Frac coef, const char *body, char *text, size_t size) {
    if (coef.num == 0) return;
    int first = text[0] == 0, negative = coef.num < 0;
    Frac magnitude = negative ? frac_neg(coef) : coef;
    text_add(text, size, first ? (negative ? "-" : "") : (negative ? " - " : " + "));
    if (!body[0]) { frac_latex(magnitude, text, size); return; }
    if (magnitude.num != 1 || magnitude.den != 1) {
        frac_latex(magnitude, text, size);
        if (isdigit((unsigned char)body[0])) text_add(text, size, " \\cdot ");
    }
    text_add(text, size, "%s", body);
}

/* Mette in text, di size byte, l'albero node scritto da put_node() (capitolo
 * 13), che lo scrive in modo che si rilegga uguale. Ritorna 0 se non ci
 * sta. Il testo della dimostrazione in corso non cambia. */
static int node_latex(const Node *node, char *text, size_t size) {
    size_t start = proof_length;
    put_node(node, 0);
    size_t length = proof_length - start;
    int fits = proof_length < PROOF_BYTES - 1 && length < size;
    if (fits) {
        memcpy(text, proof_text + start, length);
        text[length] = 0;
    }
    proof_cut(start);
    return fits;
}

/* Ritorna l'albero dell'espressione scritta in text, o NULL se non si legge.
 * Il lettore dei token resta da reimpostare. */
static Node *text_tree(const char *text) {
    Node *tree = parse_expression(text);
    if (syntax_error || failure) { syntax_error = NULL; return NULL; }
    return tree;
}

/* Ritorna una lettera che non compare in tree, per la nuova variabile di una
 * sostituzione; 0 se sono tutte prese. */
static int fresh_variable(const Node *tree) {
    static const char letters[] = "tuwvszyqrpm";
    for (const char *l = letters; *l; l++)
        if (!node_has_variable(tree, *l)) return *l;
    return 0;
}

/* Ritorna una copia di tree con quattro semplificazioni che non cambiano una
 * primitiva, utili dopo una sostituzione (la primitiva semplificata è poi
 * verificata come ogni altra):
 *
 *   - (\sqrt[n]{B})^k = \sqrt[n/g]{B}^{k/g}, con g = mcd(n, k): vale dove la
 *     radice è definita, cioè per B >= 0. \sqrt[6]{x}^{3} diventa \sqrt{x};
 *   - \arctan(\tan A) = A - k pi, con k intero costante su ogni intervallo in
 *     cui tan A è definita: le due funzioni differiscono per una costante, e
 *     come primitive sono la stessa;
 *   - e^{c \ln A} = A^c, per c un numero, dove ln A è definito: la nuova
 *     primitiva è definita in più punti, ma la verifica la confronta con f
 *     solo dove sono definite tutte e due, e f, che conteneva ln A, lo è
 *     solo dove lo è ln A;
 *   - \ln e^{A} = \ln|e^{A}| = A, per ogni A. */
static Node *tidy(const Node *tree) {
    if (!tree) return NULL;
    Node *a = tidy(tree->a), *b = tidy(tree->b);
    if (tree->kind == N_CALL && tree->op == FN_ARCTAN && a->kind == N_CALL && a->op == FN_TAN) return a->a;
    if (tree->kind == N_POW && a->kind == N_VAR && a->name == 'e') {
        /* e^{\pm \ln A} ed e^{\pm c \ln A}: per A > 0 vale A^{\pm c}. */
        const Node *exponent = b->kind == N_NEG ? b->a : b;
        Node *c = NULL, *argument = NULL;
        if (exponent->kind == N_CALL && exponent->op == FN_LN) c = node_num(1), argument = exponent->a;
        else if (exponent->kind == N_MUL && exponent->b->kind == N_CALL && exponent->b->op == FN_LN) c = exponent->a, argument = exponent->b->a;
        if (c && b->kind == N_NEG) c = node_new(N_NEG, c, NULL);
        if (c) return c->kind == N_NUM && c->value == 1 ? argument : node_new(N_POW, argument, c);
    }
    const Node *inside = tree->kind == N_CALL && tree->op == FN_LN && a->kind == N_CALL && a->op == FN_ABS ? a->a : a;
    if (tree->kind == N_CALL && tree->op == FN_LN && inside->kind == N_POW && inside->a->kind == N_VAR && inside->a->name == 'e') return inside->b;
    if (tree->kind == N_POW && a->kind == N_CALL && a->op == FN_ROOT && a->b->kind == N_NUM && b->kind == N_NUM && b->value > 0) {
        long long g = (long long)gcd128(a->b->value, b->value), n = a->b->value / g, k = b->value / g;
        Node *base = n == 1 ? a->a : node_call(FN_ROOT, a->a, node_num(n));
        return k == 1 ? base : node_new(N_POW, base, node_num(k));
    }
    Node *copy = node_new(tree->kind, a, b);
    copy->value = tree->value;
    copy->name = tree->name;
    copy->op = tree->op;
    copy->c = tree->c;
    return copy;
}

/* Scrive in text, di size byte, la primitiva G(t) scritta in inner con t
 * sostituita da h: è il ritorno alla variabile di partenza dopo una
 * sostituzione t = h(x), con le semplificazioni di tidy(). Ritorna 0 se non
 * riesce. */
static int substitute_back(const char *inner, int t, const Node *h, char *text, size_t size) {
    Node *g = text_tree(inner);
    return g && node_latex(tidy(node_replace(g, t, (Node *)h)), text, size);
}

static int primitive_text(const Node *f, int x, int depth, char *text, size_t size);

/* 30d. LE FUNZIONI RAZIONALI
 *
 * Teorema. Ogni funzione razionale N(x)/D(x) a coefficienti reali ha una
 * primitiva elementare: un polinomio, più una funzione razionale, più una
 * combinazione di logaritmi e di arcotangenti. L'algoritmo la trova, ed è
 * completo appena si sa scomporre il denominatore (Bernoulli, Leibniz; nei
 * libri: L. Torresani, "Integrazione delle funzioni razionali", pp. 1-3).
 *
 *   30d-1. Divisione: N = Q D + R con il grado di R minore di quello di D. Q
 *          si integra termine per termine.
 *
 *   30d-2. Fattori ripetuti (Hermite-Ostrogradsky). Sia D1 = mcd(D, D') e
 *          D2 = D / D1: D2 ha gli stessi fattori di D, ognuno una volta, e
 *          D1 quelli ripetuti, ognuno una volta in meno. Allora esistono, e
 *          sono unici, P di grado minore di D1 e S di grado minore di D2 con
 *
 *              R/D = (P/D1)' + S/D2,
 *
 *          cioè, moltiplicando per D = D1 D2,
 *
 *              R = P' D2 - P H + S D1,   con H = D1' D2 / D1,
 *
 *          che è un polinomio perché ogni fattore di D1 compare anche in D2.
 *          I coefficienti di P e di S sono incognite, quelli dei due membri
 *          devono coincidere: un sistema lineare con tante equazioni quante
 *          incognite, il grado di D, che si risolve con i razionali esatti.
 *          Così ciò che resta, S/D2, ha il denominatore senza fattori
 *          ripetuti (M. V. Ostrogradsky, 1845).
 *
 *   30d-3. I fattori di D2 su Q: le radici razionali, con il teorema delle
 *          radici razionali (rational_roots(), 11m); ciò che resta, se ha
 *          grado 2, è un fattore di secondo grado senza radici razionali; se
 *          ha grado 3 è irriducibile (un polinomio di terzo grado riducibile
 *          ha un fattore di primo grado); da 4 in su si cercano i fattori di
 *          secondo grado con il metodo di Kronecker (uni_quadratic_factor(),
 *          18p-6). Un fattore irriducibile di grado 3 o più ferma il metodo:
 *          le sue radici non si scrivono, e i libri non lo chiedono.
 *
 *   30d-4. Fratti semplici: S/D2 = somma di A_i / (x - r_i) e di
 *          (B_j x + C_j) / q_j(x), con un altro sistema lineare esatto.
 *
 *   30d-5. Le primitive dei fratti: A ln|x - r|; per q = x^2 + p x + s,
 *          (B x + C)/q = (B/2) q'/q + (C - B p/2)/q, e con il trinomio
 *          a x^2 + b x + c a coefficienti interi e Delta = b^2 - 4 a c:
 *
 *              \int dx / (a x^2 + b x + c) = 2 / sqrt(-Delta) arctan((2 a x + b) / sqrt(-Delta))   se Delta < 0,
 *                                          = 1 / sqrt(Delta) ln|(2 a x + b - sqrt(Delta)) / (2 a x + b + sqrt(Delta))|   se Delta > 0.
 *
 *          (Delta = 0 non capita: il trinomio avrebbe una radice razionale.)
 *
 *   30d-6. Quando un fattore resta irriducibile: se N(x)/D(x) = x^{m-1}
 *          R(x^m), con s = x^m si ha ds = m x^{m-1} dx e la primitiva è
 *          quella di R(s)/m, calcolata in s: x/(1 + x^4) diventa
 *          1/(2 (1 + s^2)).
 *
 * I conti sono tra razionali esatti a 64 bit: se escono dai limiti il
 * metodo rinuncia (fail()), non approssima. */

/* Un polinomio in una variabile a coefficienti razionali: c[0] + c[1] x +
 * ... + c[degree] x^degree. Invariante: c[degree] non è zero, i coefficienti
 * oltre degree sono zero; il polinomio nullo ha degree -1. */
typedef struct {
    int degree;
    Frac c[MAX_QPOLY + 1];
} QPoly;

/* Ritorna il polinomio nullo. */
static QPoly qpoly_zero(void) {
    QPoly p;
    p.degree = -1;
    for (int i = 0; i <= MAX_QPOLY; i++) p.c[i] = frac_int(0);
    return p;
}

/* Ristabilisce l'invariante dopo un conto che può aver annullato i
 * coefficienti più alti. */
static void qpoly_trim(QPoly *p) {
    while (p->degree >= 0 && p->c[p->degree].num == 0) p->degree--;
}

/* Ritorna a + scale b. */
static QPoly qpoly_add(QPoly a, QPoly b, Frac scale) {
    int top = a.degree > b.degree ? a.degree : b.degree;
    for (int i = 0; i <= b.degree; i++) a.c[i] = frac_add(a.c[i], frac_mul(scale, b.c[i]));
    a.degree = top;
    qpoly_trim(&a);
    return a;
}

/* Ritorna scale p. */
static QPoly qpoly_scale(QPoly p, Frac scale) { return qpoly_add(qpoly_zero(), p, scale); }

/* Ritorna a b; fallisce se il grado supera MAX_QPOLY. */
static QPoly qpoly_mul(QPoly a, QPoly b) {
    QPoly r = qpoly_zero();
    if (a.degree < 0 || b.degree < 0) return r;
    if (a.degree + b.degree > MAX_QPOLY) { fail("funzione razionale di grado troppo alto"); return r; }
    for (int i = 0; i <= a.degree; i++)
        for (int j = 0; j <= b.degree; j++) r.c[i + j] = frac_add(r.c[i + j], frac_mul(a.c[i], b.c[j]));
    r.degree = a.degree + b.degree;
    qpoly_trim(&r);
    return r;
}

/* Ritorna x^k. */
static QPoly qpoly_power_of_x(int k) {
    QPoly p = qpoly_zero();
    p.c[k] = frac_int(1);
    p.degree = k;
    return p;
}

/* Divide a per b, non nullo: mette quoziente e resto in *quotient e *rest. */
static void qpoly_divide(QPoly a, QPoly b, QPoly *quotient, QPoly *rest) {
    *quotient = qpoly_zero();
    *rest = a;
    while (rest->degree >= b.degree && !failure) {
        int shift = rest->degree - b.degree;
        Frac lead = frac_div(rest->c[rest->degree], b.c[b.degree]);
        quotient->c[shift] = lead;
        if (shift > quotient->degree) quotient->degree = shift;
        for (int j = 0; j < b.degree; j++) rest->c[j + shift] = frac_add(rest->c[j + shift], frac_neg(frac_mul(lead, b.c[j])));
        /* Il coefficiente più alto si annulla per costruzione: lo si azzera
         * a mano, così il ciclo avanza anche dopo un errore di aritmetica. */
        rest->c[rest->degree] = frac_int(0);
        qpoly_trim(rest);
    }
}

/* Ritorna la derivata di p. */
static QPoly qpoly_derivative(QPoly p) {
    QPoly d = qpoly_zero();
    for (int i = 1; i <= p.degree; i++) d.c[i - 1] = frac_mul(p.c[i], frac_int(i));
    d.degree = p.degree - 1;
    qpoly_trim(&d);
    return d;
}

/* Ritorna p diviso per il suo coefficiente più alto (p non nullo). */
static QPoly qpoly_monic(QPoly p) { return qpoly_scale(p, frac_div(frac_int(1), p.c[p.degree])); }

/* Ritorna il massimo comun divisore monico di a e b, non tutti e due nulli:
 * algoritmo di Euclide, mcd(a, b) = mcd(b, resto della divisione). */
static QPoly qpoly_gcd(QPoly a, QPoly b) {
    while (b.degree >= 0 && !failure) {
        QPoly q, r;
        qpoly_divide(a, b, &q, &r);
        a = b;
        b = r;
    }
    return qpoly_monic(a);
}

/* Ritorna p scritto a coefficienti interi senza divisori comuni e con il
 * coefficiente più alto positivo, e mette in *content il razionale per cui
 * va moltiplicato per tornare p. Fallisce se i numeri escono dai limiti. */
static QPoly qpoly_primitive(QPoly p, Frac *content) {
    __int128 g = 0, l = 1;
    for (int i = 0; i <= p.degree; i++) {
        g = gcd128(g, p.c[i].num);
        l = l / gcd128(l, p.c[i].den) * p.c[i].den;
        if (l >= COEF_LIMIT) { fail("numeri troppo grandi per il calcolo esatto"); *content = frac_int(1); return p; }
    }
    *content = p.degree < 0 ? frac_int(1) : frac_make(p.c[p.degree].num < 0 ? -g : g, l);
    return p.degree < 0 ? p : qpoly_scale(p, frac_div(frac_int(1), *content));
}

/* Legge p, un polinomio negli atomi, come polinomio nella sola variabile di
 * atomo x. Ritorna 0 se compare un altro atomo, un esponente negativo o non
 * intero, un coefficiente non reale, o se il grado supera MAX_QPOLY. */
static int qpoly_from(Poly p, int x, QPoly *out) {
    *out = qpoly_zero();
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        long long e = 0;
        if (t->mono.count > 1 || t->coef.im.num != 0) return 0;
        if (t->mono.count == 1) {
            if (t->mono.factor[0].atom != x || t->mono.factor[0].exp.den != 1) return 0;
            e = t->mono.factor[0].exp.num;
        }
        if (e < 0 || e > MAX_QPOLY) return 0;
        out->c[e] = t->coef.re;
        if (e > out->degree) out->degree = (int)e;
    }
    return 1;
}

/* Aggiunge a text, di size byte, il polinomio p nella variabile di nome
 * letter: 3x^{2} - \frac{1}{2}x + 5. Il polinomio nullo è 0. */
static void qpoly_latex(QPoly p, int letter, char *text, size_t size) {
    char sum[ANSWER_BYTES] = "", body[16];
    for (int i = p.degree; i >= 0; i--) {
        if (i == 0) body[0] = 0;
        else if (i == 1) snprintf(body, sizeof body, "%c", letter);
        else snprintf(body, sizeof body, "%c^{%d}", letter, i);
        term_latex(p.c[i], body, sum, sizeof sum);
    }
    text_add(text, size, "%s", sum[0] ? sum : "0");
}

/* Risolve il sistema lineare di n equazioni in n incognite
 * m[i][0] y_0 + ... + m[i][n-1] y_{n-1} = m[i][n], con l'eliminazione di
 * Gauss sui razionali esatti. Ritorna 1 e mette la soluzione in y[]; ritorna
 * 0 se la matrice è singolare o i numeri escono dai limiti. m viene
 * modificata. */
static int solve_linear(int n, Frac m[][MAX_QPOLY + 2], Frac *y) {
    for (int col = 0; col < n; col++) {
        /* Una riga con il pivot diverso da zero, portata al posto col. */
        int pivot = col;
        while (pivot < n && m[pivot][col].num == 0) pivot++;
        if (pivot == n) return 0;
        for (int k = 0; k <= n && pivot != col; k++) {
            Frac swap = m[col][k];
            m[col][k] = m[pivot][k];
            m[pivot][k] = swap;
        }
        /* La colonna si azzera in tutte le altre righe. */
        for (int row = 0; row < n; row++) {
            if (row == col || m[row][col].num == 0) continue;
            Frac factor = frac_div(m[row][col], m[col][col]);
            for (int k = col; k <= n; k++) m[row][k] = frac_add(m[row][k], frac_neg(frac_mul(factor, m[col][k])));
        }
        if (failure) return 0;
    }
    for (int i = 0; i < n; i++) y[i] = frac_div(m[i][n], m[i][i]);
    return !failure;
}

/* Mette in *square e *kernel i due interi con m = square^2 kernel e kernel senza
 * fattori quadrati, per m positivo fino a 10^12: sqrt(m) = square sqrt(kernel).
 * Ritorna 0 se m è troppo grande. */
static int square_part(long long m, long long *square, long long *kernel) {
    if (m <= 0 || m > 1000000000000LL) return 0;
    *square = 1;
    *kernel = 1;
    long long value = m, prime, times;
    while (pop_prime(&value, &prime, &times)) {
        for (long long k = 0; k < times / 2; k++) *square *= prime;
        if (times % 2) *kernel *= prime;
    }
    return 1;
}

/* 30d-5. Aggiunge a text la primitiva di coef / q, con q = a x^2 + b x + c a
 * coefficienti interi, a > 0, senza radici razionali: vedi la formula in
 * testa al paragrafo. letter è il nome della variabile. */
static void trinomial_latex(Frac coef, long long a, long long b, long long c, int letter, char *text, size_t size) {
    char linear[96] = "", root[48] = "", body[256];
    __int128 delta = (__int128)b * b - (__int128)4 * a * c;
    long long square, kernel;
    if (delta > (__int128)1000000000000LL || delta < -(__int128)1000000000000LL || !square_part(delta < 0 ? (long long)-delta : (long long)delta, &square, &kernel)) {
        fail("numeri troppo grandi per il calcolo esatto");
        return;
    }
    /* 2 a x + b e la radice si dividono per il loro divisore comune: il
     * rapporto non cambia, e x^2 + 1 dà arctan(x), non arctan(2x/2). */
    long long common = (long long)gcd128(gcd128(2 * a, b), square), reduced = square / common;
    QPoly line = qpoly_zero();
    line.c[1] = frac_int(2 * a / common);
    line.c[0] = frac_int(b / common);
    line.degree = 1;
    qpoly_latex(line, letter, linear, sizeof linear);

    /* sqrt(|Delta|) = square sqrt(kernel): il coefficiente diventa razionale
     * portando sqrt(kernel) al numeratore, 1/sqrt(kernel) = sqrt(kernel)/kernel. */
    if (reduced != 1) snprintf(root, sizeof root, "%lld", reduced);
    if (kernel != 1) text_add(root, sizeof root, "\\sqrt{%lld}", kernel);
    const char *outside = "";
    char radical[32] = "";
    if (kernel != 1) { snprintf(radical, sizeof radical, "\\sqrt{%lld}", kernel); outside = radical; }
    if (delta < 0) {
        coef = frac_div(frac_mul(coef, frac_int(2)), frac_int(square * kernel));
        if (root[0]) snprintf(body, sizeof body, "%s\\arctan\\left(\\frac{%s}{%s}\\right)", outside, linear, root);
        else snprintf(body, sizeof body, "%s\\arctan\\left(%s\\right)", outside, linear);
    } else {
        coef = frac_div(coef, frac_int(square * kernel));
        snprintf(body, sizeof body, "%s\\ln\\left|\\frac{%s - %s}{%s + %s}\\right|", outside, linear, root, linear, root);
    }
    term_latex(coef, body, text, size);
}

static int rational_any(QPoly num, QPoly den, int letter, char *text, size_t size, int depth);

/* 30d-6. Se num/den è x^{m-1} R(x^m) per un m >= 2 (il più grande),
 * scrive in text la primitiva, calcolata nella variabile s = x^m e riportata
 * in x. Ritorna 0 se non c'è un tale m. */
static int power_substitution(QPoly num, QPoly den, int letter, char *text, size_t size, int depth) {
    for (int m = den.degree; m >= 2; m--) {
        int fits = 1;
        for (int i = 0; i <= den.degree && fits; i++) fits = den.c[i].num == 0 || i % m == 0;
        for (int i = 0; i <= num.degree && fits; i++) fits = num.c[i].num == 0 || i % m == m - 1;
        if (!fits) continue;

        /* R(s) = Ñ(s) / D̃(s), con s^k al posto di x^{k m}; e 1/m da ds. */
        QPoly inner_num = qpoly_zero(), inner_den = qpoly_zero();
        for (int i = 0; i <= den.degree; i += m) inner_den.c[i / m] = den.c[i];
        for (int i = m - 1; i <= num.degree; i += m) inner_num.c[i / m] = frac_div(num.c[i], frac_int(m));
        inner_den.degree = den.degree / m;
        inner_num.degree = num.degree / m;
        qpoly_trim(&inner_num);
        qpoly_trim(&inner_den);

        /* La nuova variabile: una lettera diversa da quella di partenza. */
        int s = letter == 's' ? 'u' : 's';
        char inner[ANSWER_BYTES] = "";
        if (!rational_any(inner_num, inner_den, s, inner, sizeof inner, depth + 1)) return 0;
        Node *power = node_new(N_POW, node_new(N_VAR, NULL, NULL), node_num(m));
        power->a->name = letter;
        return substitute_back(inner, s, power, text, size);
    }
    return 0;
}

/* 30d. Scrive in text, di size byte, una primitiva di num/den (den non
 * nullo) nella variabile di nome letter, con l'algoritmo in testa al
 * paragrafo. Ritorna 1 se ci riesce, 0 se un fattore di den resta
 * irriducibile o i numeri escono dai limiti. */
static int rational_primitive(QPoly num, QPoly den, int letter, char *text, size_t size, int depth) {
    /* La matrice dei due sistemi lineari: statica perché è grande (10 KB)
     * per la pila di una ricerca ricorsiva. Non è mai in uso durante una
     * chiamata ricorsiva: ogni sistema si risolve prima di andare avanti. */
    static Frac m[MAX_QPOLY + 1][MAX_QPOLY + 2];
    Frac y[MAX_QPOLY + 1];
    char power_text[16];
    text[0] = 0;
    if (depth > MAX_PRIMITIVE_DEPTH) return 0;

    /* La frazione ai minimi termini: i fattori comuni darebbero una
     * primitiva giusta ma scritta male, come t^2 / t^3. Toglierli cambia la
     * funzione solo nei punti in cui non era definita. */
    if (num.degree >= 0) {
        QPoly common = qpoly_gcd(num, den), unused_rest;
        qpoly_divide(num, common, &num, &unused_rest);
        qpoly_divide(den, common, &den, &unused_rest);
    }

    /* Il denominatore monico; poi 30d-1, la divisione. */
    Frac lead = frac_div(frac_int(1), den.c[den.degree]);
    num = qpoly_scale(num, lead);
    den = qpoly_scale(den, lead);
    QPoly quotient, rest, unused;
    qpoly_divide(num, den, &quotient, &rest);
    for (int k = quotient.degree; k >= 0; k--) {
        if (k == 0) snprintf(power_text, sizeof power_text, "%c", letter);
        else snprintf(power_text, sizeof power_text, "%c^{%d}", letter, k + 1);
        term_latex(frac_div(quotient.c[k], frac_int(k + 1)), power_text, text, size);
    }
    if (rest.degree < 0) return !failure;

    /* 30d-2. Hermite-Ostrogradsky, se den ha fattori ripetuti. */
    QPoly d1 = qpoly_gcd(den, qpoly_derivative(den)), d2, s = rest;
    qpoly_divide(den, d1, &d2, &unused);
    if (d1.degree > 0 && !failure) {
        QPoly h;
        qpoly_divide(qpoly_mul(qpoly_derivative(d1), d2), d1, &h, &unused);
        int n = den.degree, unknowns_p = d1.degree;
        for (int j = 0; j < n && !failure; j++) {
            /* La colonna dell'incognita j: un coefficiente di P o di S. */
            QPoly column;
            if (j < unknowns_p) {
                QPoly power = qpoly_power_of_x(j);
                column = qpoly_add(qpoly_mul(qpoly_derivative(power), d2), qpoly_mul(power, h), frac_int(-1));
            } else {
                column = qpoly_mul(qpoly_power_of_x(j - unknowns_p), d1);
            }
            for (int i = 0; i < n; i++) m[i][j] = column.c[i];
        }
        for (int i = 0; i < n; i++) m[i][n] = rest.c[i];
        if (failure || !solve_linear(n, m, y)) return 0;

        /* P/D1, scritta con coefficienti interi sopra e sotto. */
        QPoly p = qpoly_zero();
        s = qpoly_zero();
        for (int j = 0; j < unknowns_p; j++) p.c[j] = y[j];
        for (int j = unknowns_p; j < n; j++) s.c[j - unknowns_p] = y[j];
        p.degree = unknowns_p - 1;
        s.degree = d2.degree - 1;
        qpoly_trim(&p);
        qpoly_trim(&s);
        if (p.degree >= 0) {
            /* Ai minimi termini, a coefficienti interi, con la costante
             * dentro la frazione: -\frac{4}{x - 2}, \frac{9}{4x^{4}}. */
            Frac top, bottom;
            QPoly common = qpoly_gcd(p, d1), reduced_p, reduced_d1;
            qpoly_divide(p, common, &reduced_p, &unused);
            qpoly_divide(d1, common, &reduced_d1, &unused);
            QPoly p_int = qpoly_primitive(reduced_p, &top), d1_int = qpoly_primitive(reduced_d1, &bottom);
            Frac scale = frac_div(top, bottom);
            p_int = qpoly_scale(p_int, frac_int(scale.num < 0 ? -scale.num : scale.num));
            d1_int = qpoly_scale(d1_int, frac_int(scale.den));
            char fraction[ANSWER_BYTES] = "\\frac{";
            qpoly_latex(p_int, letter, fraction, sizeof fraction);
            text_add(fraction, sizeof fraction, "}{");
            qpoly_latex(d1_int, letter, fraction, sizeof fraction);
            text_add(fraction, sizeof fraction, "}");
            term_latex(frac_int(scale.num < 0 ? -1 : 1), fraction, text, size);
        }
        if (s.degree < 0) return !failure;
    }
    if (failure) return 0;

    /* 30d-3. I fattori di d2: prima le radici razionali. */
    Frac root[MAX_QPOLY + 2];
    QPoly quadratic[MAX_QPOLY / 2 + 1], left = d2;
    int roots = 0, quadratics = 0;
    {
        Frac content;
        QPoly whole = qpoly_primitive(d2, &content);
        long long c[MAX_UNIVARIATE + 1];
        if (whole.degree > MAX_UNIVARIATE) return 0;
        for (int i = 0; i <= whole.degree; i++) {
            if (whole.c[i].num > LLONG_MAX / 4 || whole.c[i].num < -(LLONG_MAX / 4)) return 0;
            c[i] = whole.c[i].num;
        }
        roots = rational_roots(c, whole.degree, root);
        if (roots < 0) return 0;
        for (int i = 0; i < roots && !failure; i++) {
            QPoly linear = qpoly_zero(), q, r;
            linear.c[1] = frac_int(1);
            linear.c[0] = frac_neg(root[i]);
            linear.degree = 1;
            qpoly_divide(left, linear, &q, &r);
            left = q;
        }
    }

    /* Poi i fattori di secondo grado: ciò che resta, o i fattori di
     * Kronecker; un fattore irriducibile di grado 3 o più ferma tutto, e
     * resta da provare 30d-6. */
    if (left.degree >= 4 && !failure) {
        Frac content;
        QPoly whole = qpoly_primitive(left, &content);
        Uni u = {whole.degree, {0}}, factor, quotient_uni;
        for (int i = 0; i <= whole.degree; i++) u.c[i] = whole.c[i].num;
        while (u.degree >= 4 && !failure && uni_quadratic_factor(&u, &factor, &quotient_uni)) {
            QPoly q = qpoly_zero();
            for (int i = 0; i <= 2; i++) q.c[i] = frac_make(factor.c[i], 1);
            q.degree = 2;
            quadratic[quadratics++] = qpoly_monic(q);
            u = quotient_uni;
        }
        left = qpoly_zero();
        for (int i = 0; i <= u.degree; i++) left.c[i] = frac_make(u.c[i], 1);
        left.degree = u.degree;
        qpoly_trim(&left);
    }
    if (left.degree == 2) quadratic[quadratics++] = qpoly_monic(left);
    else if (left.degree >= 3 || failure) return 0;

    /* 30d-4. Fratti semplici: le colonne d2/(x - r_i), x d2/q_j e d2/q_j. */
    int n = d2.degree, column = 0;
    for (int i = 0; i < roots && !failure; i++, column++) {
        QPoly linear = qpoly_zero(), q, r;
        linear.c[1] = frac_int(1);
        linear.c[0] = frac_neg(root[i]);
        linear.degree = 1;
        qpoly_divide(d2, linear, &q, &r);
        for (int k = 0; k < n; k++) m[k][column] = q.c[k];
    }
    for (int j = 0; j < quadratics && !failure; j++) {
        QPoly q, r;
        qpoly_divide(d2, quadratic[j], &q, &r);
        QPoly shifted = qpoly_mul(q, qpoly_power_of_x(1));
        for (int k = 0; k < n; k++) {
            m[k][column] = shifted.c[k];
            m[k][column + 1] = q.c[k];
        }
        column += 2;
    }
    if (failure || column != n) return 0;
    for (int k = 0; k < n; k++) m[k][n] = s.c[k];
    if (!solve_linear(n, m, y)) return 0;

    /* 30d-5. Le primitive dei fratti. Un fattore x - u/v si scrive v x - u:
     * cambia il logaritmo di una costante, che si perde nella c. */
    for (int i = 0; i < roots && !failure; i++) {
        char body[128] = "\\ln\\left|";
        QPoly linear = qpoly_zero();
        linear.c[1] = frac_int(root[i].den);
        linear.c[0] = frac_int(-root[i].num);
        linear.degree = 1;
        qpoly_latex(linear, letter, body, sizeof body);
        text_add(body, sizeof body, "\\right|");
        term_latex(y[i], body, text, size);
    }
    for (int j = 0; j < quadratics && !failure; j++) {
        /* q_j = x^2 + p x + q, e il trinomio intero a x^2 + b x + c. */
        Frac b_coef = y[roots + 2 * j], c_coef = y[roots + 2 * j + 1], content;
        QPoly whole = qpoly_primitive(quadratic[j], &content);
        long long a = whole.c[2].num, b = whole.c[1].num, c = whole.c[0].num;
        char body[256] = "";
        __int128 delta = (__int128)b * b - (__int128)4 * a * c;

        /* (B/2) ln q: per Delta < 0 il trinomio è sempre positivo. */
        snprintf(body, sizeof body, delta < 0 ? "\\ln\\left(" : "\\ln\\left|");
        qpoly_latex(whole, letter, body, sizeof body);
        text_add(body, sizeof body, delta < 0 ? "\\right)" : "\\right|");
        term_latex(frac_div(b_coef, frac_int(2)), body, text, size);

        /* (C - B p/2) / q = a (C - B p/2) / (a x^2 + b x + c). */
        Frac rest_coef = frac_add(c_coef, frac_neg(frac_mul(b_coef, frac_div(quadratic[j].c[1], frac_int(2)))));
        trinomial_latex(frac_mul(rest_coef, frac_int(a)), a, b, c, letter, text, size);
    }
    return !failure;
}

/* 30d. La primitiva di num/den: con rational_primitive(), e se un fattore
 * del denominatore resta irriducibile con la sostituzione s = x^m (30d-6).
 * Ritorna 1 se una delle due riesce. */
static int rational_any(QPoly num, QPoly den, int letter, char *text, size_t size, int depth) {
    if (rational_primitive(num, den, letter, text, size, depth)) return 1;
    failure = NULL;
    text[0] = 0;
    if (power_substitution(num, den, letter, text, size, depth)) return 1;
    failure = NULL;
    return 0;
}

/* 30d. Il metodo per la ricerca: se f, calcolata con i conti esatti, è una
 * funzione razionale di x a coefficienti razionali, ne scrive in text una
 * primitiva. */
static int rational_method(const Node *f, int x, int depth, char *text, size_t size) {
    env_count = 0;
    Rat value = eval(f);
    Poly num, den;
    QPoly n, d;
    if (failure || !rat_polynomials(value, &num, &den) || !qpoly_from(num, atom_var(x), &n) || !qpoly_from(den, atom_var(x), &d) || d.degree < 0) {
        failure = NULL;
        return 0;
    }
    int found = rational_any(n, d, x, text, size, depth);
    failure = NULL;
    if (found) primitive_method = "con i fratti semplici";
    return found;
}

/* 30e. I POLINOMI PER ESPONENZIALI
 *
 * Teorema. Per n naturale e lambda complesso diverso da zero
 *
 *     \int x^n e^{lambda x} dx = e^{lambda x} \sum_{k=0}^{n} (-1)^k n!/(n-k)! x^{n-k} / lambda^{k+1}.
 *
 * È ciò che danno n integrazioni per parti, e si controlla derivando: con
 * c_k = (-1)^k n!/((n-k)! lambda^{k+1}), la derivata di e^{lambda x} c_k
 * x^{n-k} è e^{lambda x} (lambda c_k x^{n-k} + (n-k) c_k x^{n-k-1}), e
 * lambda c_k = -(n-k+1) c_{k-1}: le due parti si cancellano a catena, e
 * resta lambda c_0 x^n e^{lambda x} = x^n e^{lambda x}. Per lambda = 0 è
 * x^{n+1}/(n+1).
 *
 * Che cosa ci entra. Il valore di f calcolato con i conti esatti è un
 * polinomio negli atomi; seni e coseni vi sono già esponenziali complessi,
 * sin(b x) = (e^{i b x} - e^{-i b x}) / (2 i) (capitolo 11), e i prodotti e
 * le potenze sono già sviluppati. Se ogni termine è c x^n e^{a x} e^{i b x},
 * con n naturale, a e b razionali e c un numero (eventualmente moltiplicato
 * per costanti come e o \sqrt{2}), la formula si applica termine per
 * termine. Ci entrano così, con lo stesso conto, le potenze di seni e
 * coseni (le formule di bisezione), i prodotti di seni e coseni di angoli
 * diversi (le formule di Werner), x^n sin(b x) e x^n e^{a x} (per parti, più
 * volte), e^{a x} sin(b x) (il caso "ciclico" dei libri, dove l'integrale
 * torna uguale a se stesso dopo due passi).
 *
 * Il ritorno ai numeri reali. La primitiva ha termini d e^{i b x} e d'
 * e^{-i b x}; se la funzione è reale lo è anche lei, e la coppia vale
 * (d + d') cos(b x) + i (d - d') sin(b x), con due coefficienti reali. Se
 * non lo sono la funzione non era reale, e il metodo rinuncia. */

/* Un termine della primitiva: coef x^power e^{(a + i b) x} constant. */
typedef struct {
    int power;       /* l'esponente di x, da 0 in su */
    Frac a, b;       /* l'esponenziale e^{(a + i b) x} */
    Mono constant;   /* il prodotto degli atomi che non dipendono da x */
    Num coef;        /* il coefficiente, complesso */
} ExpTerm;

static ExpTerm exp_term[MAX_EXP_TERMS];
static int exp_terms;

/* Aggiunge alla primitiva il termine coef x^power e^{(a + i b) x}
 * constant, sommandolo a quello con gli stessi esponenti se c'è già. */
static void exp_term_add(int power, Frac a, Frac b, const Mono *constant, Num coef) {
    for (int i = 0; i < exp_terms; i++) {
        ExpTerm *t = &exp_term[i];
        if (t->power == power && frac_cmp(t->a, a) == 0 && frac_cmp(t->b, b) == 0 && mono_cmp(&t->constant, constant) == 0) {
            t->coef = num_add(t->coef, coef);
            return;
        }
    }
    if (exp_terms == MAX_EXP_TERMS) { fail("primitiva con troppi termini"); return; }
    exp_term[exp_terms++] = (ExpTerm){power, a, b, *constant, coef};
}

/* Prototipo in avanti necessario: la base di un atomo è un polinomio, fatto
 * di atomi. */
static int poly_involves(Poly p, int x);

/* Ritorna 1 se l'atomo dipende dall'atomo x, a qualunque livello: è x, o
 * x compare nella sua base, nel suo esponente o nel suo argomento. Per
 * prudenza le somme e le successioni ne dipendono sempre. */
static int atom_involves(int atom, int x) {
    const Atom *a = &atoms[atom];
    if (atom == x) return 1;
    switch (a->kind) {
    case ATOM_VAR: return 0;
    case ATOM_ATAN: return poly_involves(atan_args[a->id].num, x) || poly_involves(atan_args[a->id].den, x);
    case ATOM_POW: case ATOM_LN:
        for (int i = 0; a->kind == ATOM_POW && i < a->exponent.count; i++)
            if (atom_involves(a->exponent.factor[i].atom, x)) return 1;
        if (a->base == BASE_ATOM) return atom_involves((int)a->id, x);
        return a->base == BASE_POLY && poly_involves(base_polys[a->id], x);
    default: return 1;
    }
}

static int poly_involves(Poly p, int x) {
    for (int i = 0; i < p.count; i++)
        for (int f = 0; f < p.term[i].mono.count; f++)
            if (atom_involves(p.term[i].mono.factor[f].atom, x)) return 1;
    return 0;
}

/* Mette in text, di size byte, il monomio m scritto da put_mono() (capitolo
 * 13); ritorna 0 se non ci sta o se contiene qualcosa che non si scrive. */
static int mono_latex(const Mono *m, char *text, size_t size) {
    size_t start = proof_length;
    unwritable = 0;
    if (m->count) put_mono(m);
    size_t length = proof_length - start;
    int fits = !unwritable && proof_length < PROOF_BYTES - 1 && length < size;
    if (fits) {
        memcpy(text, proof_text + start, length);
        text[length] = 0;
    }
    proof_cut(start);
    return fits;
}

/* 30e. Il metodo per la ricerca: vedi la testa del paragrafo. */
static int exponential_method(const Node *f, int x, int depth, char *text, size_t size) {
    (void)depth;
    env_count = 0;
    Rat value = eval(f);
    int xa = atom_var(x), e = atom_var('e');
    exp_terms = 0;
    if (failure || !poly_is_one(value.den)) { failure = NULL; return 0; }

    /* Ogni termine: c x^n e^{a x} e^{i b x} per le costanti; si integra
     * subito con la formula. */
    for (int i = 0; i < value.num.count && !failure; i++) {
        const Term *t = &value.num.term[i];
        int n = 0;
        Frac a = frac_int(0), b = frac_int(0);
        Mono constant;
        constant.count = 0;
        for (int k = 0; k < t->mono.count; k++) {
            const Factor *factor = &t->mono.factor[k];
            const Atom *atom = &atoms[factor->atom];
            int linear = atom->kind == ATOM_POW && atom->exponent.count == 1 && atom->exponent.factor[0].atom == xa &&
                         frac_cmp(atom->exponent.factor[0].exp, frac_int(1)) == 0;
            /* Un atomo 1^M vale 1: nasce da power(), che calcola e^{u} come
             * il quoziente delle potenze di numeratore e denominatore di e,
             * e il denominatore è 1. */
            if (atom->kind == ATOM_POW && atom->base == BASE_POLY && poly_is_one(base_polys[atom->id])) continue;
            if (factor->atom == xa && factor->exp.den == 1 && factor->exp.num >= 0) n = (int)factor->exp.num;
            else if (linear && atom->base == BASE_EI) b = frac_add(b, factor->exp);
            else if (linear && atom->base == BASE_ATOM && atom->id == e) a = frac_add(a, factor->exp);
            else if (!atom_involves(factor->atom, xa)) { Mono single = mono_atom(factor->atom, factor->exp); constant = mono_mul(&constant, &single); }
            else return 0;
        }
        if (n > MAX_POWER) return 0;
        if (a.num == 0 && b.num == 0) {
            exp_term_add(n + 1, a, b, &constant, num_mul(t->coef, num_frac((Frac){1, n + 1})));
            continue;
        }
        /* lambda = a + i b, e i termini c_k della formula. */
        Num inverse = num_inv((Num){a, b}), step = num_mul(t->coef, inverse);
        for (int k = 0; k <= n && !failure; k++) {
            exp_term_add(n - k, a, b, &constant, step);
            step = num_mul(num_mul(step, inverse), num_int(-(n - k)));
        }
    }
    if (failure) { failure = NULL; return 0; }

    /* Il ritorno ai reali: per ogni termine con b >= 0 il suo compagno con
     * -b, e i due coefficienti reali del coseno e del seno. */
    text[0] = 0;
    for (int i = 0; i < exp_terms && !failure; i++) {
        ExpTerm *t = &exp_term[i];
        if (t->b.num < 0 && t->power >= 0) {
            /* Senza un compagno con +b: lo si crea, con coefficiente zero. */
            Frac plus = frac_neg(t->b);
            exp_term_add(t->power, t->a, plus, &t->constant, num_int(0));
        }
    }
    for (int i = 0; i < exp_terms && !failure; i++) {
        ExpTerm *t = &exp_term[i];
        if (t->b.num < 0) continue;
        Num partner = num_int(0);
        for (int j = 0; j < exp_terms; j++) {
            const ExpTerm *u = &exp_term[j];
            if (t->b.num != 0 && u->power == t->power && frac_cmp(u->a, t->a) == 0 && frac_cmp(u->b, frac_neg(t->b)) == 0 &&
                mono_cmp(&u->constant, &t->constant) == 0)
                partner = u->coef;
        }
        Num cosine = t->b.num ? num_add(t->coef, partner) : t->coef;
        Num difference_ = num_add(t->coef, num_neg(partner));
        Num sine = {frac_neg(difference_.im), difference_.re};
        if (cosine.im.num != 0 || (t->b.num != 0 && sine.im.num != 0)) { failure = NULL; return 0; }

        /* Il corpo comune: costanti, x^m, e^{a x}; poi cos e sin di b x. */
        char body[512] = "", piece[160] = "";
        if (!mono_latex(&t->constant, body, sizeof body)) return 0;
        /* Una costante puo finire con un comando senza graffe, come \pi:
         * accostarle x o e scriverebbe \pix o \pie, comandi diversi. Il
         * prodotto esplicito conserva i fattori anche quando si rileggono. */
        if (body[0] && (t->power > 0 || t->a.num != 0)) text_add(body, sizeof body, " \\cdot ");
        if (t->power == 1) text_add(body, sizeof body, "%c", x);
        else if (t->power > 1) text_add(body, sizeof body, "%c^{%d}", x, t->power);
        if (t->a.num != 0) {
            char letter[2] = {(char)x, 0};
            term_latex(t->a, letter, piece, sizeof piece);
            text_add(body, sizeof body, "e^{%s}", piece);
        }
        if (t->b.num == 0) { term_latex(cosine.re, body, text, size); continue; }
        char angle[96] = "", trig[768];
        char letter[2] = {(char)x, 0};
        term_latex(t->b, letter, angle, sizeof angle);
        snprintf(trig, sizeof trig, "%s\\cos\\left(%s\\right)", body, angle);
        term_latex(cosine.re, trig, text, size);
        snprintf(trig, sizeof trig, "%s\\sin\\left(%s\\right)", body, angle);
        term_latex(sine.re, trig, text, size);
    }
    if (failure) { failure = NULL; return 0; }
    if (!text[0]) snprintf(text, size, "0");
    primitive_method = "con i polinomi per esponenziali";
    return 1;
}

/* 30f. PER PARTI
 *
 * Teorema. Se u e v sono derivabili su un intervallo,
 *
 *     \int u v' dx = u v - \int u' v dx,
 *
 * perché (u v)' = u' v + u v'. La regola di scelta dei libri: u è il
 * fattore che derivando si semplifica, v' quello che si sa integrare. Qui u
 * è un logaritmo o un'arcotangente L (anche una sua potenza L^k), la cui
 * derivata è razionale nell'argomento, e v' è tutto il resto P: ci si
 * aspetta che V = \int P dx non contenga più logaritmi né arcotangenti (un
 * polinomio, una funzione razionale), e allora resta \int V (L^k)' dx, che
 * ha L^{k-1} al posto di L^k. x^2 ln x, ln(1 + x^2), x arctan(1 + 16 x),
 * arctan(x)/x^2, ln^2 x si fanno così.
 *
 * I prodotti con un esponenziale, un seno o un coseno (x^3 e^x, e^x sin x)
 * non passano di qui: sono il paragrafo 30e, che li fa tutti con una
 * formula. */

/* Ritorna 1 se il nodo è un logaritmo o un'arcotangente di un argomento con
 * x, o una sua potenza a esponente intero positivo scritto come numero. */
static int is_log_like(const Node *node, int x) {
    if (node->kind == N_POW && node->b->kind == N_NUM && node->b->value >= 1) node = node->a;
    return node->kind == N_CALL && (node->op == FN_LN || node->op == FN_LOG || node->op == FN_ARCTAN) && node_has_variable(node->a, x);
}

/* Ritorna 1 se in tree compare un logaritmo o un'arcotangente di x. */
static int has_log_like(const Node *tree, int x) {
    if (!tree) return 0;
    if (is_log_like(tree, x)) return 1;
    return has_log_like(tree->a, x) || has_log_like(tree->b, x) || has_log_like(tree->c, x);
}

/* Cerca tra i fattori di tree (prodotti, numeratori, segni meno) quelli che
 * is_log_like() accetta: li conta in *count e mette l'ultimo in *found. */
static void log_factors(const Node *tree, int x, const Node **found, int *count) {
    if (is_log_like(tree, x)) { *found = tree; (*count)++; return; }
    if (tree->kind == N_MUL) { log_factors(tree->a, x, found, count); log_factors(tree->b, x, found, count); }
    else if (tree->kind == N_DIV || tree->kind == N_NEG) log_factors(tree->a, x, found, count);
}

/* Ritorna una copia di tree, in cui target è un fattore (come per
 * node_is_factor(), 9j), con target sostituito da 1. */
static Node *drop_factor(Node *tree, const Node *target) {
    if (tree == target) return node_num(1);
    if (tree->kind == N_MUL && tree->a == target) return tree->b;
    if (tree->kind == N_MUL && tree->b == target) return tree->a;
    if (tree->kind == N_MUL) return node_is_factor(tree->a, target) ? node_new(N_MUL, drop_factor(tree->a, target), tree->b)
                                                                   : node_new(N_MUL, tree->a, drop_factor(tree->b, target));
    if (tree->kind == N_DIV || tree->kind == N_NEG) return node_new(tree->kind, drop_factor(tree->a, target), tree->b);
    return tree;
}

/* 30f. Il metodo per la ricerca: vedi la testa del paragrafo. */
static int parts_method(const Node *f, int x, int depth, char *text, size_t size) {
    const Node *log = NULL;
    int count = 0;
    Node *folded = node_fold(f, &(int){1});
    log_factors(folded, x, &log, &count);
    if (count != 1) return 0;
    Node *rest = drop_factor(folded, log);
    if (has_log_like(rest, x)) return 0;

    /* V = \int P, che non deve avere logaritmi; poi \int V L'. */
    char inner[ANSWER_BYTES], tail[ANSWER_BYTES];
    if (!primitive_text(rest, x, depth + 1, inner, sizeof inner)) return 0;
    Node *v = text_tree(inner);
    if (!v || has_log_like(v, x)) return 0;
    Node *slope = derive(strip_log_abs(log), x);
    if (failure) { failure = NULL; return 0; }
    if (!primitive_text(node_new(N_MUL, v, slope), x, depth + 1, tail, sizeof tail)) return 0;
    Node *g = text_tree(tail);
    if (!g || !node_latex(node_new(N_SUB, node_new(N_MUL, v, (Node *)log), g), text, size)) return 0;
    primitive_method = "per parti";
    return 1;
}

/* 30g. PER SOSTITUZIONE
 *
 * Teorema. Se G è una primitiva di g e h è derivabile, allora
 *
 *     \int g(h(x)) h'(x) dx = G(h(x)) + c,
 *
 * perché (G(h(x)))' = g(h(x)) h'(x) per la regola della catena.
 *
 * Come si riconosce h (la "derivata che divide"). Per ogni funzione interna
 * h dell'integranda f (l'argomento di una funzione, la base o l'esponente di
 * una potenza, una funzione intera come ln x o sin x) si calcola q = f / h'
 * e, nel suo albero, si scrive t al posto di ogni h. Se ciò che resta non
 * dipende più da x, cioè la sua derivata rispetto a x si riduce a zero con
 * i conti esatti, allora q = g(h(x)) con g(t) quel che resta, e la primitiva
 * è G(h(x)), con G cercata nella variabile t. È il caso di x e^{2x^2 - 1}
 * (h = 2x^2 - 1), di 1/(x sqrt(ln x)) (h = ln x), di R(cos x) sin x
 * (h = cos x).
 *
 * Le sostituzioni che rendono la funzione razionale. Quando ogni radice
 * dell'integranda ha lo stesso radicando a x + b, con t = (a x + b)^{1/n}
 * (n il minimo comune multiplo degli indici) le radici diventano potenze di
 * t, x = (t^n - b)/a e dx = (n/a) t^{n-1} dt. Quando ogni potenza con x
 * all'esponente ha la stessa base B e un esponente lineare, con
 * t = B^{g x} (g il massimo comun divisore dei coefficienti) le potenze
 * diventano potenze di t e dx = dt / (g ln(B) t). In tutti e due i casi
 * la funzione nella nuova variabile è spesso razionale (30d), o ha una
 * radice di un polinomio di primo grado in t, e si ricomincia. */

/* Ritorna una copia di tree in cui ogni sotto-albero scritto come h è la
 * lettera t. */
static Node *replace_subtree(const Node *tree, const Node *h, Node *t) {
    if (!tree) return NULL;
    if (node_equal(tree, h)) return t;
    Node *copy = node_new(tree->kind, replace_subtree(tree->a, h, t), replace_subtree(tree->b, h, t));
    copy->value = tree->value;
    copy->name = tree->name;
    copy->op = tree->op;
    copy->c = replace_subtree(tree->c, h, t);
    return copy;
}

/* Aggiunge a list[] (di *count posti, al più MAX_INNER) le funzioni
 * interne di tree che contengono x: le chiamate di funzione, le potenze con
 * x, i loro argomenti, basi ed esponenti. x stessa e i doppioni no. */
static void collect_candidates(const Node *tree, int x, const Node **list, int *count) {
    if (!tree || !node_has_variable(tree, x)) return;
    const Node *own[3] = {NULL, NULL, NULL};
    if (tree->kind == N_CALL || tree->kind == N_POW) { own[0] = tree; own[1] = tree->a; own[2] = tree->kind == N_POW ? tree->b : NULL; }
    for (int i = 0; i < 3; i++) {
        const Node *h = own[i];
        if (!h || !node_has_variable(h, x) || (h->kind == N_VAR && h->name == x)) continue;
        int seen = 0;
        for (int j = 0; j < *count && !seen; j++) seen = node_equal(list[j], h);
        if (!seen && *count < MAX_INNER) list[(*count)++] = h;
    }
    collect_candidates(tree->a, x, list, count);
    collect_candidates(tree->b, x, list, count);
}

/* Ritorna l'albero del razionale v. */
static Node *frac_node(Frac v) {
    Node *n = node_num(v.num < 0 ? -v.num : v.num);
    if (v.den != 1) n = node_new(N_DIV, n, node_num(v.den));
    return v.num < 0 ? node_new(N_NEG, n, NULL) : n;
}

/* Ritorna l'albero della lettera name. */
static Node *letter_node(int name) {
    Node *n = node_new(N_VAR, NULL, NULL);
    n->name = name;
    return n;
}

/* Ritorna 1 se tree, calcolato con i conti esatti, vale zero dove è
 * definito; 0 se non lo si dimostra. */
static int tree_vanishes(const Node *tree) {
    env_count = 0;
    Rat value = eval(tree);
    int zero = !failure && poly_vanishes(value.num);
    failure = NULL;
    return zero;
}

/* Ritorna il fattore di tree (come per node_is_factor(), 9j) scritto come
 * target, o NULL se non c'è. */
static const Node *find_factor(const Node *tree, const Node *target) {
    if (node_equal(tree, target)) return tree;
    if (tree->kind == N_MUL) {
        const Node *found = find_factor(tree->a, target);
        return found ? found : find_factor(tree->b, target);
    }
    return tree->kind == N_DIV || tree->kind == N_NEG ? find_factor(tree->a, target) : NULL;
}

/* Scrive la derivata slope come c g, con c senza x: scende per i segni, i
 * prodotti per un fattore senza x e i quozienti per una costante. Mette in
 * *core il nucleo g (x^1 diventa x) e ritorna l'albero di c. */
static Node *slope_constant(const Node *slope, int x, const Node **core) {
    if (slope->kind == N_NEG) return node_new(N_NEG, slope_constant(slope->a, x, core), NULL);
    if (slope->kind == N_MUL && !node_has_variable(slope->a, x)) return node_new(N_MUL, slope->a, slope_constant(slope->b, x, core));
    if (slope->kind == N_MUL && !node_has_variable(slope->b, x)) return node_new(N_MUL, slope_constant(slope->a, x, core), slope->b);
    if (slope->kind == N_DIV && !node_has_variable(slope->b, x)) return node_new(N_DIV, slope_constant(slope->a, x, core), slope->b);
    *core = slope->kind == N_POW && slope->b->kind == N_NUM && slope->b->value == 1 ? slope->a : slope;
    return node_num(1);
}

/* 30g. La derivata che divide: vedi la testa del paragrafo. Se h' = c g e g
 * è scritta come un fattore di f, q è f senza quel fattore, diviso c (si
 * evita una divisione che resterebbe scritta, come sin(x)/sin(x)); se
 * h = ln x, la x che resta è e^t. */
static int substitution_method(const Node *f, int x, int depth, char *text, size_t size) {
    const Node *candidate[MAX_INNER];
    int count = 0, t = fresh_variable(f);
    collect_candidates(f, x, candidate, &count);
    for (int i = 0; i < count && t; i++) {
        const Node *h = candidate[i];
        Node *slope = derive(strip_log_abs(h), x);
        if (failure) { failure = NULL; continue; }
        const Node *core;
        Node *constant = slope_constant(node_fold(slope, &(int){1}), x, &core);
        const Node *factor = find_factor(f, core);
        Node *quotient = factor ? node_new(N_DIV, drop_factor((Node *)f, factor), constant) : node_new(N_DIV, (Node *)f, slope);
        Node *q = replace_subtree(quotient, h, letter_node(t));
        if (h->kind == N_CALL && h->op == FN_LN && h->a->kind == N_VAR && h->a->name == x)
            q = node_replace(q, x, node_new(N_POW, letter_node('e'), letter_node(t)));

        /* Se resta x, deve essere solo apparente: la derivata rispetto a x
         * si annulla, e allora si dà a x un valore qualsiasi in cui q si
         * calcola. */
        if (node_has_variable(q, x)) {
            Node *change = derive(strip_log_abs(q), x);
            if (failure) { failure = NULL; continue; }
            if (!tree_vanishes(change)) continue;
            Node *fixed = NULL;
            for (int p = 0; p < PRIMITIVE_POINTS && !fixed; p++) {
                Node *attempt = node_replace(q, x, frac_node(primitive_points[p]));
                env_count = 0;
                eval(attempt);
                if (!failure) fixed = attempt;
                failure = NULL;
            }
            if (!fixed) continue;
            q = fixed;
        }

        /* G nella variabile t, poi t = h. */
        char inner[ANSWER_BYTES];
        if (!primitive_text(q, t, depth + 1, inner, sizeof inner)) continue;
        if (!substitute_back(inner, t, h, text, size)) continue;
        primitive_method = "per sostituzione";
        return 1;
    }
    return 0;
}

/* I nodi radice raccolti da collect_roots(): \sqrt[k]{B} e B^{p/q}. */
typedef struct {
    const Node *node;  /* il nodo della radice, o della potenza */
    long long index;   /* l'indice k, o il denominatore q */
    long long power;   /* 1 per una radice, il numeratore p per una potenza */
} RootNode;

/* Aggiunge a list[] le radici di tree con x nel radicando: \sqrt[k]{B} con k
 * numero, e B^{e} con e un razionale non intero senza x. Ritorna 0 se ce ne
 * sono troppe. */
static int collect_roots(const Node *tree, int x, RootNode *list, int *count) {
    if (!tree || !node_has_variable(tree, x)) return 1;
    long long index = 0, power = 1;
    if (tree->kind == N_CALL && tree->op == FN_ROOT && node_has_variable(tree->a, x)) {
        if (tree->b->kind != N_NUM || tree->b->value < 2) return 0;
        index = tree->b->value;
    } else if (tree->kind == N_POW && node_has_variable(tree->a, x) && !node_has_variable(tree->b, x)) {
        env_count = 0;
        Num e;
        int numeric = rat_number(eval(tree->b), &e);
        failure = NULL;
        if (numeric && e.im.num == 0 && e.re.den != 1) { index = e.re.den; power = e.re.num; }
    }
    if (index) {
        if (*count == MAX_INNER) return 0;
        list[(*count)++] = (RootNode){tree, index, power};
    }
    return collect_roots(tree->a, x, list, count) && collect_roots(tree->b, x, list, count);
}

/* Ritorna una copia di tree con le radici di list[] scritte come potenze di
 * t (la radice di indice k è t^{n/k}) e x sostituita da value. */
static Node *rationalize(const Node *tree, int x, const RootNode *list, int count, long long n, Node *t, Node *value) {
    if (!tree) return NULL;
    for (int i = 0; i < count; i++)
        if (list[i].node == tree) return node_new(N_POW, t, frac_node(frac_make((__int128)n * list[i].power, list[i].index)));
    if (tree->kind == N_VAR && tree->name == x) return value;
    Node *copy = node_new(tree->kind, rationalize(tree->a, x, list, count, n, t, value), rationalize(tree->b, x, list, count, n, t, value));
    copy->value = tree->value;
    copy->name = tree->name;
    copy->op = tree->op;
    copy->c = tree->c;
    return copy;
}

/* 30g. t = (a x + b)^{1/n}: vedi la testa del paragrafo. */
static int root_method(const Node *f, int x, int depth, char *text, size_t size) {
    RootNode root[MAX_INNER];
    int count = 0, t = fresh_variable(f);
    if (!t || !collect_roots(f, x, root, &count) || count == 0) return 0;

    /* Lo stesso radicando, di primo grado in x: B = a x + b. */
    env_count = 0;
    Rat base = eval(root[0].node->a);
    Poly num, den;
    QPoly linear;
    if (failure || !rat_polynomials(base, &num, &den) || !poly_is_one(den) || !qpoly_from(num, atom_var(x), &linear) || linear.degree != 1) { failure = NULL; return 0; }
    long long n = 1;
    for (int i = 0; i < count; i++) {
        env_count = 0;
        Rat other = eval(root[i].node->a);
        if (failure || !poly_vanishes(rat_add(other, base, 1).num)) { failure = NULL; return 0; }
        n = n / (long long)gcd128(n, root[i].index) * root[i].index;
        if (n > MAX_UNI) return 0;
    }

    /* x = (t^n - b)/a e dx = (n/a) t^{n-1} dt. */
    Frac a = linear.c[1], b = linear.c[0];
    Node *tn = node_new(N_POW, letter_node(t), node_num(n));
    Node *value = node_new(N_DIV, node_new(N_SUB, tn, frac_node(b)), frac_node(a));
    Node *inside = rationalize(f, x, root, count, n, letter_node(t), value);
    Node *g = node_new(N_MUL, frac_node(frac_div(frac_int(n), a)), node_new(N_MUL, inside, node_new(N_POW, letter_node(t), node_num(n - 1))));
    if (failure) { failure = NULL; return 0; }

    /* G(t), poi t = radice n-esima di a x + b. */
    char inner[ANSWER_BYTES];
    if (!primitive_text(g, t, depth + 1, inner, sizeof inner)) return 0;
    Node *back = node_call(FN_ROOT, (Node *)root[0].node->a, node_num(n));
    if (!substitute_back(inner, t, back, text, size)) return 0;
    primitive_method = "per sostituzione, con una radice";
    return 1;
}

/* Aggiunge a list[] le potenze di tree con x all'esponente e la base senza
 * x. Ritorna 0 se sono troppe. */
static int collect_exponentials(const Node *tree, int x, const Node **list, int *count) {
    if (!tree || !node_has_variable(tree, x)) return 1;
    if (tree->kind == N_POW && !node_has_variable(tree->a, x)) {
        if (*count == MAX_INNER) return 0;
        list[(*count)++] = tree;
        return 1;
    }
    return collect_exponentials(tree->a, x, list, count) && collect_exponentials(tree->b, x, list, count);
}

/* Ritorna una copia di tree con ogni potenza di list[] sostituita da
 * replacement[] nella stessa posizione. */
static Node *replace_listed(const Node *tree, const Node **list, Node **replacement, int count) {
    if (!tree) return NULL;
    for (int i = 0; i < count; i++)
        if (list[i] == tree) return replacement[i];
    Node *copy = node_new(tree->kind, replace_listed(tree->a, list, replacement, count), replace_listed(tree->b, list, replacement, count));
    copy->value = tree->value;
    copy->name = tree->name;
    copy->op = tree->op;
    copy->c = tree->c;
    return copy;
}

/* 30g. t = B^{g x}: vedi la testa del paragrafo. */
static int exponential_substitution(const Node *f, int x, int depth, char *text, size_t size) {
    const Node *power[MAX_INNER];
    Node *replacement[MAX_INNER];
    Frac slope[MAX_INNER], shift[MAX_INNER];
    int count = 0, t = fresh_variable(f), xa = atom_var(x);
    if (!t || !collect_exponentials(f, x, power, &count) || count == 0) return 0;

    /* La stessa base, positiva (o e), ed esponenti a x + b con a e b
     * razionali; g è il massimo comun divisore degli a. */
    env_count = 0;
    Rat base = eval(power[0]->a);
    Num value;
    int euler = power[0]->a->kind == N_VAR && power[0]->a->name == 'e';
    if (failure || (!euler && (!rat_number(base, &value) || value.im.num != 0 || value.re.num <= 0 || frac_cmp(value.re, frac_int(1)) == 0))) { failure = NULL; return 0; }
    __int128 top = 0, bottom = 1;
    for (int i = 0; i < count; i++) {
        env_count = 0;
        Rat other = eval(power[i]->a), exponent = eval(power[i]->b);
        Poly num, den;
        QPoly line;
        if (failure || !poly_vanishes(rat_add(other, base, 1).num) || !rat_polynomials(exponent, &num, &den) || !poly_is_one(den) ||
            !qpoly_from(num, xa, &line) || line.degree != 1) { failure = NULL; return 0; }
        slope[i] = line.c[1];
        shift[i] = line.c[0];
        top = gcd128(top, slope[i].num);
        bottom = bottom / gcd128(bottom, slope[i].den) * slope[i].den;
        if (bottom > MAX_POWER) return 0;
    }
    Frac g = frac_make(top, bottom);

    /* B^{a x + b} = B^b t^{a/g}; x non deve restare. */
    for (int i = 0; i < count; i++) {
        Frac k = frac_div(slope[i], g);
        Node *piece = frac_cmp(k, frac_int(1)) == 0 ? letter_node(t) : node_new(N_POW, letter_node(t), frac_node(k));
        if (shift[i].num != 0) piece = node_new(N_MUL, node_new(N_POW, power[i]->a, frac_node(shift[i])), piece);
        replacement[i] = piece;
    }
    Node *inside = replace_listed(f, power, replacement, count);
    if (failure || node_has_variable(inside, x)) { failure = NULL; return 0; }

    /* dx = dt / (g ln(B) t): la costante davanti, perché la linearità la
     * porti fuori. */
    Node *logarithm_of_base = node_call(FN_LN, power[0]->a, NULL);
    if (frac_cmp(g, frac_int(1)) != 0) logarithm_of_base = node_new(N_MUL, frac_node(g), logarithm_of_base);
    Node *constant = euler ? frac_node(frac_div(frac_int(1), g)) : node_new(N_DIV, node_num(1), logarithm_of_base);
    Node *integrand = node_new(N_MUL, constant, node_new(N_DIV, inside, letter_node(t)));
    char inner[ANSWER_BYTES];
    if (!primitive_text(integrand, t, depth + 1, inner, sizeof inner)) return 0;
    Node *back = node_new(N_POW, power[0]->a, node_new(N_MUL, frac_node(g), letter_node(x)));
    if (frac_cmp(g, frac_int(1)) == 0) back->b = letter_node(x);
    if (!substitute_back(inner, t, back, text, size)) return 0;
    primitive_method = "per sostituzione, con un esponenziale";
    return 1;
}

/* 30h. SENO E COSENO: t = tan(x/2)
 *
 * Teorema. Se t = tan(theta/2) e theta non è un multiplo dispari di pi,
 *
 *     e^{i theta} = cos(theta) + i sin(theta) = (1 + i t) / (1 - i t),
 *
 * perché cos(theta) = (1 - t^2)/(1 + t^2) e sin(theta) = 2 t/(1 + t^2), e
 * (1 + i t)^2 = (1 - t^2) + 2 i t. Inoltre d theta = 2 dt / (1 + t^2). Una
 * funzione razionale di seno e coseno di theta, che nei conti esatti è una
 * frazione di polinomi negli esponenziali e^{i k theta} (capitolo 11),
 * diventa così una funzione razionale di t (a coefficienti complessi, ma il
 * suo valore è reale: la si moltiplica sopra e sotto per il coniugato del
 * denominatore), e si integra con 30d.
 *
 * L'angolo theta. Gli esponenti di e^{i x} che compaiono sono multipli
 * interi di un razionale g, il loro massimo comun divisore, e theta = g x.
 * Se inoltre, sopra e sotto, sono tutti pari o tutti dispari (in unità di
 * g), la funzione non cambia sommando pi/g a x, ed è una funzione di
 * e^{2 i g x}: allora theta = 2 g x, e t = tan(g x). È la regola di Bioche
 * per tan x, e dà primitive più corte: tan^2 x e 1/(sin^2 x cos^2 x) sono
 * razionali in tan x.
 *
 * La primitiva vale dove tan(theta/2) è definita: tra due multipli dispari
 * consecutivi di pi, ed è la verifica a dirlo, come sempre. */

/* Ritorna il polinomio (1 + i t)^p (1 - i t)^q nell'atomo t. */
static Poly cayley_factor(int t, int p, int q) {
    Term term;
    term.coef = num_int(1);
    term.mono = mono_atom(t, frac_int(1));
    Poly plus = poly_add(poly_const(num_int(1)), poly_mul(poly_const((Num){frac_int(0), frac_int(1)}), poly_term(term)), 0);
    Poly minus = poly_add(poly_const(num_int(1)), poly_mul(poly_const((Num){frac_int(0), frac_int(1)}), poly_term(term)), 1);
    Poly r = poly_const(num_int(1));
    for (int i = 0; i < p; i++) r = poly_mul(r, plus);
    for (int i = 0; i < q; i++) r = poly_mul(r, minus);
    return r;
}

/* Ritorna il coniugato di p: i coefficienti con la parte immaginaria
 * cambiata di segno (gli atomi sono lettere reali). */
static Poly poly_conjugate(Poly p) {
    Poly r = poly_add(poly_const(num_int(0)), p, 0);
    for (int i = 0; i < r.count; i++) r.term[i].coef.im = frac_neg(r.term[i].coef.im);
    return r;
}

/* Legge l'esponente di e^{i x} nel termine t, in *e: ritorna 0 se il termine
 * contiene qualcos'altro. ei è l'atomo e^{i x}. */
static int trig_exponent(const Term *t, int ei, Frac *e) {
    *e = frac_int(0);
    for (int k = 0; k < t->mono.count; k++) {
        if (t->mono.factor[k].atom != ei) return 0;
        *e = t->mono.factor[k].exp;
    }
    return 1;
}

/* L'intero k per cui il termine t, c e^{i e x}, è c w^k con w = e^{i theta}:
 * k = (e/g - odd)/2 con la regola di Bioche (bioche = 1), k = e/g senza.
 * ei è l'atomo e^{i x}. */
static long long trig_power(const Term *t, int ei, Frac g, int bioche, int odd) {
    Frac e;
    trig_exponent(t, ei, &e);
    long long k = frac_div(e, g).num;
    return bioche ? (k - odd) / 2 : k;
}

/* Riscrive la somma p di termini c w^k come polinomio nell'atomo t,
 * moltiplicata per (1 + i t)^M (1 - i t)^M: con w = (1 + i t)/(1 - i t),
 * w^k (1 + i t)^M (1 - i t)^M = (1 + i t)^{M+k} (1 - i t)^{M-k}, che per
 * |k| <= M è un polinomio. Gli altri argomenti come per trig_power(). */
static Poly cayley_poly(Poly p, int ei, Frac g, int bioche, int odd, long long big, int t) {
    Poly r = poly_const(num_int(0));
    for (int i = 0; i < p.count && !failure; i++) {
        long long k = trig_power(&p.term[i], ei, g, bioche, odd);
        r = poly_add(r, poly_mul(poly_const(p.term[i].coef), cayley_factor(t, (int)(big + k), (int)(big - k))), 0);
    }
    return r;
}

/* 30h. Il metodo per la ricerca: vedi la testa del paragrafo. */
static int trig_method(const Node *f, int x, int depth, char *text, size_t size) {
    env_count = 0;
    Rat value = eval(f);
    int t = fresh_variable(f);
    if (failure || !t) { failure = NULL; return 0; }
    Mono angle = mono_atom(atom_var(x), frac_int(1));
    int ei = atom_pow(BASE_EI, 0, &angle), ta = atom_var(t);

    /* Negli atomi solo e^{i x}; g è il massimo comun divisore degli
     * esponenti, e parity[side] la parità comune di e/g sopra (0) e sotto
     * (1), oppure 2 se non sono tutti uguali. */
    __int128 top = 0, bottom = 1;
    for (int side = 0; side < 2; side++) {
        Poly p = side ? value.den : value.num;
        for (int i = 0; i < p.count; i++) {
            Frac e;
            if (!trig_exponent(&p.term[i], ei, &e)) return 0;
            top = gcd128(top, e.num);
            bottom = bottom / gcd128(bottom, e.den) * e.den;
            if (bottom > MAX_POWER) return 0;
        }
    }
    if (top == 0) return 0;
    Frac g = frac_make(top, bottom);
    int parity[2] = {-1, -1};
    for (int side = 0; side < 2; side++) {
        Poly p = side ? value.den : value.num;
        for (int i = 0; i < p.count; i++) {
            int odd = (int)(trig_power(&p.term[i], ei, g, 0, 0) % 2 != 0);
            parity[side] = parity[side] < 0 || parity[side] == odd ? odd : 2;
        }
    }
    int bioche = parity[0] == parity[1] && parity[0] < 2, odd = bioche ? parity[0] : 0;
    Frac theta = bioche ? frac_mul(g, frac_int(2)) : g;

    /* M, il più grande |k|; poi i due polinomi in t. */
    long long big = 0;
    for (int side = 0; side < 2; side++) {
        Poly p = side ? value.den : value.num;
        for (int i = 0; i < p.count; i++) {
            long long k = trig_power(&p.term[i], ei, g, bioche, odd);
            if (k > big) big = k;
            if (-k > big) big = -k;
        }
    }
    if (big > MAX_QPOLY / 4 - 1) return 0;
    Poly above = cayley_poly(value.num, ei, g, bioche, odd, big, ta), below = cayley_poly(value.den, ei, g, bioche, odd, big, ta);

    /* Reali: sopra e sotto per il coniugato del denominatore. */
    Poly conjugate = poly_conjugate(below);
    above = poly_mul(above, conjugate);
    below = poly_mul(below, conjugate);
    QPoly n, d;
    if (failure || !qpoly_from(above, ta, &n) || !qpoly_from(below, ta, &d) || d.degree < 0) { failure = NULL; return 0; }

    /* dx = 2 dt / (theta (1 + t^2)), con theta il coefficiente di x. */
    QPoly unit_circle = qpoly_zero();
    unit_circle.c[0] = unit_circle.c[2] = frac_int(1);
    unit_circle.degree = 2;
    n = qpoly_scale(n, frac_int(2));
    d = qpoly_mul(qpoly_scale(d, theta), unit_circle);
    char inner[ANSWER_BYTES] = "";
    if (failure || !rational_any(n, d, t, inner, sizeof inner, depth + 1)) { failure = NULL; return 0; }

    /* t = tan(theta x / 2). */
    Frac half = frac_div(theta, frac_int(2));
    Node *argument = letter_node(x);
    if (half.num != 1) argument = node_new(N_MUL, node_num(half.num), argument);
    if (half.den != 1) argument = node_new(N_DIV, argument, node_num(half.den));
    static char label[128];
    char written[64];
    if (!substitute_back(inner, t, node_call(FN_TAN, argument, NULL), text, size) || !node_latex(argument, written, sizeof written)) return 0;
    snprintf(label, sizeof label, "con la sostituzione t = \\tan\\left(%s\\right)", written);
    primitive_method = label;
    return 1;
}

/* 30c-1. Una costante: la primitiva di c è c x. */
static int constant_method(const Node *f, int x, int depth, char *text, size_t size) {
    (void)depth;
    if (node_has_variable(f, x)) return 0;
    primitive_method = "per linearità";
    if (f->kind == N_NUM && f->value == 1) return node_latex(letter_node(x), text, size);
    return node_latex(node_new(N_MUL, (Node *)f, letter_node(x)), text, size);
}

/* 30c-2. Un segno o un fattore senza x si portano fuori dall'integrale. */
static int factor_method(const Node *f, int x, int depth, char *text, size_t size) {
    char inner[ANSWER_BYTES];
    const Node *inside = NULL, *constant = NULL;
    if (f->kind == N_NEG) inside = f->a, constant = node_num(-1);
    else if (f->kind == N_MUL && !node_has_variable(f->a, x)) inside = f->b, constant = f->a;
    else if (f->kind == N_MUL && !node_has_variable(f->b, x)) inside = f->a, constant = f->b;
    else if (f->kind == N_DIV && !node_has_variable(f->b, x)) inside = f->a, constant = node_new(N_DIV, node_num(1), f->b);
    Node *g;
    if (!inside || !primitive_text(inside, x, depth, inner, sizeof inner) || !(g = text_tree(inner))) return 0;
    const char *method = primitive_method;
    if (!node_latex(node_new(N_MUL, (Node *)constant, g), text, size)) return 0;
    primitive_method = method;
    return 1;
}

/* 30c-8. Una somma, un termine alla volta. */
static int sum_method(const Node *f, int x, int depth, char *text, size_t size) {
    char inner[ANSWER_BYTES], other[ANSWER_BYTES];
    Node *g, *h;
    if (f->kind != N_ADD && f->kind != N_SUB) return 0;
    if (!primitive_text(f->a, x, depth, inner, sizeof inner) || !(g = text_tree(inner))) return 0;
    if (!primitive_text(f->b, x, depth, other, sizeof other) || !(h = text_tree(other))) return 0;
    primitive_method = "per linearità";
    return node_latex(node_new(f->kind, g, h), text, size);
}

/* I metodi della ricerca, nell'ordine in cui si provano (vedi la testa di
 * 30c): le funzioni razionali e i polinomi per esponenziali vengono prima
 * della linearità, perché assorbono da sé i fattori numerici e danno
 * primitive più corte.
 *
 * Warning: se aggiungi un metodo, aggiungilo anche all'elenco in testa a 30c
 * e al commento di design del capitolo. */
static int (*const primitive_methods[])(const Node *, int, int, char *, size_t) = {
    constant_method, rational_method, exponential_method, factor_method, parts_method,
    substitution_method, root_method, exponential_substitution, trig_method, sum_method,
};

/* Quante chiamate a primitive_text() restano per l'enunciato in corso. Ogni
 * metodo può chiamarla su altre funzioni, e senza un tetto i tentativi
 * crescerebbero come una potenza della profondità: finito il conto, la
 * ricerca si arrende. */
static int primitive_budget;

/* 30c. Scrive in text, di size byte, una primitiva di f nella variabile x,
 * provando i metodi di primitive_methods[] uno dopo l'altro. Ritorna 1 se
 * uno riesce. Ciò che scrive non è ancora verificato.
 *
 * Ciò che un tentativo lascia nell'arena e nella tabella degli atomi si
 * toglie prima del successivo, e anche alla fine: il risultato è un testo,
 * che non dipende da nessuno dei due. Gli atomi sono al più MAX_ATOMS, e i
 * tentativi abbandonati li esaurirebbero. */
static int primitive_text(const Node *f, int x, int depth, char *text, size_t size) {
    text[0] = 0;
    if (depth > MAX_PRIMITIVE_DEPTH || failure || primitive_budget <= 0) return 0;
    primitive_budget--;
    Scratch mark = scratch_mark();
    int found = 0;
    for (size_t i = 0; i < sizeof primitive_methods / sizeof *primitive_methods && !found; i++) {
        found = primitive_methods[i](f, x, depth, text, size);
        if (!found) text[0] = 0;
        failure = NULL;
        scratch_drop(mark);
    }
    return found;
}

/* 30i. GLI INTEGRALI DEFINITI
 *
 * Le ipotesi del teorema fondamentale (in testa al capitolo) si controllano
 * con gli intervalli del capitolo 24. [a, b] si divide in RIEMANN_PIECES
 * parti uguali, e su ognuna, I, si calcola la serie di Taylor di f fino al
 * secondo ordine con gli intervalli (27h), su tutto I in una volta. Se il
 * calcolo riesce, ogni operazione è stata fatta dentro il suo dominio per
 * ogni x di I: nessun denominatore si annulla, ogni logaritmo ha l'argomento
 * positivo, ogni radice il radicando positivo. Le funzioni elementari sono
 * analitiche dove sono definite così, quindi f lo è in un intorno di ogni
 * punto di I. Dove il calcolo non riesce la parte si dimezza, fino a
 * RIEMANN_SPLITS volte. Lo stesso per F.
 *
 * Perché gli intervalli e non la tabella dei segni (18p). Il risultato è lo
 * stesso, "non si annulla su [a, b]", ma qui gli estremi sono spesso numeri
 * come pi/2, e le funzioni seni e coseni ristretti a un intervallo, che la
 * tabella tratta solo in casi particolari (18p-14). Con gli intervalli il
 * metodo è uno solo per ogni funzione, ed è completo per ciò che serve: se f
 * è continua su [a, b] con ogni sua parte lontana dai bordi del proprio
 * dominio, per compattezza ne è lontana di una quantità positiva, e
 * dimezzando abbastanza gli intervalli la vedono. Se il calcolo non riesce
 * (uno zero proprio in un estremo, un integrale improprio) l'integrale passa
 * a 30k, che lo tratta come improprio, mai un sì sbagliato: \sqrt{x} su
 * [0, 1] è continua, ma in 0 non è analitica, e qui non la si accetta; come
 * integrale improprio su (0, 1) sì, con lo stesso valore.
 *
 * L'INVOLUCRO DI RIEMANN, il controllo indipendente
 *
 * Su ogni parte I di ampiezza w, con punto medio m:
 *
 *   - l'integrale di f su I sta tra w min f e w max f, cioè in w f(I), e
 *     f(I) è chiuso nell'intervallo della serie al grado 0;
 *   - per la formula di Taylor con il resto di Lagrange,
 *     f(x) = f(m) + f'(m)(x - m) + f''(xi)/2 (x - m)^2 con xi in I; il
 *     termine di primo grado ha integrale zero su I, e (x - m)^2 ha
 *     integrale w^3/12. Quindi l'integrale sta in w f(m) + C w^3/12, con
 *     C l'intervallo del coefficiente di grado 2 della serie su I.
 *
 * Tutte e due le stime sono garantite (il valore vero sta di sicuro
 * dentro), quindi anche la loro intersezione; la somma sulle parti chiude
 * l'integrale. Se è troppo larga si ricomincia con quattro volte tante
 * parti. Non usa F, né le regole di derivazione, né i conti esatti: per
 * questo può controllare F(b) - F(a), e da sola basta a dire FALSO quando il
 * valore scritto ne è di sicuro fuori. */

/* L'esito dei conti con gli intervalli su [a, b]. */
typedef struct {
    int defined;     /* 1 se f, e F se data, sono analitiche su tutto [a, b] */
    int broken;      /* 1 se due stime garantite non si toccano: un errore del programma */
    Range integral;  /* contiene l'integrale di f da a a b, se defined */
} Enclosure;

/* Aggiunge a e->integral l'integrale di f sulla parte da p a q, di ampiezza
 * width (gli estremi e l'ampiezza sono intervalli che contengono i numeri
 * veri), dimezzandola fino a splits volte dove il calcolo non riesce. f e F
 * sono già passati da sample_tree(). */
static void enclose_piece(Enclosure *e, const Node *f, const Node *F, int x, Range p, Range q, Range width, int splits) {
    Range hull = {p.low, q.high}, two = range_ratio(2, 1);
    int undefined = 0;
    Range values = node_range(f, x, hull, &undefined);
    if (!range_known(values) || (F && !range_known(sample_value(F, x, hull)))) {
        Range middle = range_div(range_add(p, q), two), half = range_div(width, two);
        if (splits == 0 || !range_known(middle)) { e->defined = 0; return; }
        enclose_piece(e, f, F, x, p, middle, half, splits - 1);
        if (e->defined) enclose_piece(e, f, F, x, middle, q, half, splits - 1);
        return;
    }

    /* Le due stime, e la loro intersezione. La seconda vuole f due volte
     * derivabile su tutta la parte: c'è solo dove la serie si calcola. */
    Jet series = jet_eval(f, x, hull, 2);
    Range plain = range_mul(width, values);
    Range cube = range_div(range_mul(range_mul(width, width), width), range_ratio(12, 1));
    Range sharp = range_add(range_mul(width, sample_value(f, x, range_div(range_add(p, q), two))), range_mul(series.c[2], cube));
    Range piece = plain;
    if (range_known(sharp)) {
        piece.low = plain.low > sharp.low ? plain.low : sharp.low;
        piece.high = plain.high < sharp.high ? plain.high : sharp.high;
        if (piece.low > piece.high) { e->broken = 1; e->defined = 0; return; }
    }
    e->integral = range_add(e->integral, piece);
}

/* Ritorna l'involucro dell'integrale di f da a a b, con a < b, e controlla
 * che f e F (se non è NULL) siano analitiche su [a, b]: vedi la testa di
 * 30i. Le parti sono RIEMANN_PIECES, e quattro volte tante finché
 * l'involucro è più largo di 10^-9 volte (1 + |integrale|), fino a most. */
static Enclosure riemann_enclosure(const Node *f, const Node *F, int x, Range a, Range b, long long most) {
    Enclosure e = {1, 0, {0, 0}};
    for (long long pieces = RIEMANN_PIECES; pieces <= most; pieces *= 4) {
        Range span = range_sub(b, a), width = range_div(span, range_ratio(pieces, 1));
        e = (Enclosure){1, 0, {0, 0}};
        for (long long k = 0; k < pieces && e.defined; k++) {
            Range p = range_add(a, range_mul(span, range_ratio(k, pieces))), q = range_add(a, range_mul(span, range_ratio(k + 1, pieces)));
            enclose_piece(&e, f, F, x, p, q, width, RIEMANN_SPLITS);
        }
        if (!e.defined || !range_known(e.integral)) { e.defined = 0; return e; }
        double size = e.integral.high > -e.integral.low ? e.integral.high : -e.integral.low;
        if (e.integral.high - e.integral.low <= 1e-9 * (1 + size)) break;
    }
    return e;
}

/* 30i-1. I VALORI ESATTI NEGLI ESTREMI
 *
 * F(b) - F(a) si calcola con i conti esatti, legando x al valore esatto
 * dell'estremo; per gli angoli noti si scrivono prima i valori esatti di
 * seni, coseni e arcotangenti (exact_angles()). */

/* I valori esatti di seno e coseno negli angoli k pi/12, per k da 0 a 6
 * (da 0 a 90 gradi), che i libri ricavano dai triangoli con gli angoli di
 * 30, 45 e 60 gradi, e da quelli con le formule di bisezione:
 * cos(pi/12) = sqrt((1 + cos(pi/6))/2) = (sqrt(6) + sqrt(2))/4. */
static const char *const angle_sine[7] = {"0", "\\frac{\\sqrt{6} - \\sqrt{2}}{4}", "\\frac{1}{2}", "\\frac{\\sqrt{2}}{2}",
                                          "\\frac{\\sqrt{3}}{2}", "\\frac{\\sqrt{6} + \\sqrt{2}}{4}", "1"};

/* Ritorna l'albero del valore esatto di sin (cosine = 0) o di cos
 * (cosine = 1) nell'angolo k pi/12, per ogni intero k: con
 * sin(pi - u) = sin u, sin(u + pi) = -sin u e cos u = sin(pi/2 - u). */
static Node *angle_value(long long k, int cosine) {
    if (cosine) k = 6 - k;
    k %= 24;
    if (k < 0) k += 24;
    int negative = k >= 12;
    if (negative) k -= 12;
    if (k > 6) k = 12 - k;
    Node *v = text_tree(angle_sine[k]);
    return negative ? node_new(N_NEG, v, NULL) : v;
}

/* Le tangenti degli angoli k pi/12, per k da 1 a 5: tan(pi/12) = 2 - sqrt(3)
 * e tan(5 pi/12) = 2 + sqrt(3) vengono dalla formula di bisezione,
 * tan(u/2) = (1 - cos u)/sin u. */
static const char *const angle_tangent[6] = {"0", "2 - \\sqrt{3}", "\\frac{\\sqrt{3}}{3}", "1", "\\sqrt{3}", "2 + \\sqrt{3}"};

/* Ritorna una copia di tree in cui ogni seno, coseno, tangente o cotangente
 * il cui argomento, con x legata a value, vale k pi/12 con k intero, è
 * scritto con il suo valore esatto (angle_value()), e ogni arcotangente di
 * una delle tangenti di angle_tangent[] (o della sua opposta) è scritta come
 * l'angolo. Perché: nei conti esatti sin(pi/6) è una combinazione
 * dell'atomo e^{i pi/6}, che il test di annullamento non sa ridurre a 1/2
 * (gli mancano le relazioni tra le radici dell'unità), e arctan(sqrt(3)/3) è
 * un atomo che la sua regola 12c non sa confrontare con pi/6. */
static Node *exact_angles(const Node *tree, int x, Rat value) {
    if (!tree) return NULL;
    Node *copy = node_new(tree->kind, exact_angles(tree->a, x, value), exact_angles(tree->b, x, value));
    copy->value = tree->value;
    copy->name = tree->name;
    copy->op = tree->op;
    copy->c = tree->c;
    int trig = tree->kind == N_CALL && (tree->op == FN_SIN || tree->op == FN_COS || tree->op == FN_TAN || tree->op == FN_COT);
    if (!trig && !(tree->kind == N_CALL && tree->op == FN_ARCTAN)) return copy;
    env_count = 0;
    env_push(x, value);
    Rat angle = eval(tree->a);
    env_count = 0;
    if (failure) { failure = NULL; return copy; }

    /* L'arcotangente: l'argomento confrontato con le tangenti note. */
    if (!trig) {
        for (int k = 1; k <= 5; k++) {
            Rat tangent = eval(text_tree(angle_tangent[k]));
            Node *turn = node_new(N_DIV, node_new(N_MUL, node_num(k), letter_node(VAR_PI)), node_num(12));
            if (!failure && poly_vanishes(rat_add(angle, tangent, 1).num)) return turn;
            if (!failure && poly_vanishes(rat_add(angle, tangent, 0).num)) return node_new(N_NEG, turn, NULL);
            failure = NULL;
        }
        return copy;
    }

    /* L'argomento di seno e coseno deve essere q pi, con 12 q intero. */
    Num q;
    int pi = atom_var(VAR_PI);
    if (!poly_is_one(angle.den)) return copy;
    if (angle.num.count == 0) q = num_int(0);
    else if (angle.num.count != 1 || angle.num.term[0].mono.count != 1 || angle.num.term[0].mono.factor[0].atom != pi ||
             frac_cmp(angle.num.term[0].mono.factor[0].exp, frac_int(1)) != 0) return copy;
    else q = angle.num.term[0].coef;
    Frac k = frac_mul(q.re, frac_int(12));
    if (q.im.num != 0 || k.den != 1) return copy;
    Node *sine = angle_value(k.num, 0), *cosine = angle_value(k.num, 1);
    if (tree->op == FN_SIN) return sine;
    if (tree->op == FN_COS) return cosine;
    return tree->op == FN_TAN ? node_new(N_DIV, sine, cosine) : node_new(N_DIV, cosine, sine);
}

/* Ritorna il valore esatto di tree con x legata a value, con i seni e i
 * coseni degli angoli noti già scritti con i loro valori (exact_angles()). */
static Rat value_at(const Node *tree, int x, Rat value) {
    Node *known = exact_angles(tree, x, value);
    env_count = 0;
    env_push(x, value);
    Rat r = eval(known);
    env_count = 0;
    return r;
}

/* Ritorna p senza i fattori 1^M, che valgono 1: nascono da power() (vedi
 * exponential_method()) e scritti si leggerebbero \left(1\right)^{-10\,\pi}. */
static Poly poly_without_ones(Poly p) {
    Poly r = poly_const(num_int(0));
    for (int i = 0; i < p.count && !failure; i++) {
        Term t = p.term[i];
        Mono kept;
        kept.count = 0;
        for (int k = 0; k < t.mono.count; k++) {
            const Atom *a = &atoms[t.mono.factor[k].atom];
            if (a->kind != ATOM_POW || a->base != BASE_POLY || !poly_is_one(base_polys[a->id])) kept.factor[kept.count++] = t.mono.factor[k];
        }
        t.mono = kept;
        r = poly_add(r, poly_term(t), 0);
    }
    return r;
}

/* Mette in text, di size byte, il numero r scritto da put_rat() (capitolo
 * 13), senza i fattori 1^M; ritorna 0 se non ci sta o non si scrive. */
static int rat_latex(Rat r, char *text, size_t size) {
    r = (Rat){poly_without_ones(r.num), poly_without_ones(r.den)};
    size_t start = proof_length;
    unwritable = 0;
    put_rat(r);
    size_t length = proof_length - start;
    int fits = !unwritable && proof_length < PROOF_BYTES - 1 && length < size;
    if (fits) {
        memcpy(text, proof_text + start, length);
        text[length] = 0;
    }
    proof_cut(start);
    return fits;
}

/* Aggiunge alla dimostrazione l'intervallo r come [low, high], con abbastanza
 * cifre. */
static void put_range(Range r) { proof_add("\\left[%.16g, %.16g\\right]", r.low, r.high); }

/* 30i-2. I VALORI ASSOLUTI: SPEZZARE L'INTERVALLO
 *
 * |u| non è derivabile dove u si annulla, e una primitiva di |x - 1| non è
 * una formula sola. Ma tra due zeri consecutivi di u il segno di u è
 * costante (u è continua), e lì |u| = u oppure |u| = -u: l'integrale su
 * [a, b] è la somma degli integrali sulle parti, ognuno con una funzione
 * senza valore assoluto, a cui si applica il teorema fondamentale.
 *
 * Gli zeri di u si cercano dove si sa: la radice di u se è di primo grado
 * in x (anche con pi tra i coefficienti, come 6x - pi), le radici razionali
 * se è un polinomio, i multipli di pi/12 se contiene seni e coseni. La
 * ricerca è euristica; ciò che si usa no:
 *
 *   - ogni zero z è uno zero esatto: u(z) = 0 con il test di annullamento;
 *   - tra due punti consecutivi u non si annulla: vicino a uno zero z la
 *     serie di Taylor di u su [z, z + delta] (con gli intervalli) dà u' di
 *     segno certo, quindi u è monotona e si annulla solo in z; nel resto
 *     della parte gli intervalli danno a u un segno certo, lo stesso.
 *
 * Se uno zero sfugge alla ricerca il secondo controllo fallisce, e il
 * verdetto è NON DIMOSTRATO. */

/* Una parte [p, q] dell'intervallo di integrazione, con la funzione che
 * vi coincide con f: f stessa, o f con il valore assoluto tolto. */
typedef struct {
    Rat p, q;          /* gli estremi, esatti */
    Range low, high;   /* gli stessi, con gli intervalli */
    Node *f;           /* la funzione da integrare sulla parte */
} Stretch;

/* Raccoglie in list[] (al più MAX_INNER) i valori assoluti di tree che non
 * sono dentro un logaritmo: quelli lo derive() li attraversa (30a). */
static void collect_abs(const Node *tree, const Node **list, int *count) {
    if (!tree || (tree->kind == N_CALL && (tree->op == FN_LN || tree->op == FN_LOG))) return;
    if (tree->kind == N_CALL && tree->op == FN_ABS && *count < MAX_INNER) list[(*count)++] = tree;
    collect_abs(tree->a, list, count);
    collect_abs(tree->b, list, count);
}

/* Ritorna l'intervallo che contiene il numero r, o "non so". */
static Range rat_range(Rat r) { return range_div(poly_range(r.num), poly_range(r.den)); }

/* Ritorna 1 se in tree compare un seno, un coseno, una tangente o una
 * cotangente. */
static int has_trig(const Node *tree) {
    if (!tree) return 0;
    if (tree->kind == N_CALL && (tree->op == FN_SIN || tree->op == FN_COS || tree->op == FN_TAN || tree->op == FN_COT)) return 1;
    return has_trig(tree->a) || has_trig(tree->b) || has_trig(tree->c);
}

/* Mette in *sign il segno di u, certo e lo stesso, su tutta la parte da lo a
 * hi (intervalli che contengono gli estremi veri), dividendola fino a splits
 * volte. Ritorna 0 se non lo trova. */
static int range_sign(const Node *u, int x, Range lo, Range hi, int splits, int *sign) {
    int undefined = 0, side;
    Range value = node_range(u, x, (Range){lo.low, hi.high}, &undefined);
    if (range_side(value, &side)) {
        if (*sign == 0) *sign = side;
        return side == *sign;
    }
    if (splits == 0) return 0;
    Range middle = range_div(range_add(lo, hi), range_ratio(2, 1));
    return range_known(middle) && range_sign(u, x, lo, middle, splits - 1, sign) && range_sign(u, x, middle, hi, splits - 1, sign);
}

/* Mette in *sign il segno di u sulla parte aperta da lo a hi, dove u vale
 * zero in lo se zero_low, in hi se zero_high: vedi la testa di 30i-2.
 * Ritorna 0 se non si riesce a stabilirlo. */
static int piece_sign(const Node *u, int x, Range lo, Range hi, int zero_low, int zero_high, int *sign) {
    Range width = range_sub(hi, lo);
    *sign = 0;
    for (int end = 0; end < 2; end++) {
        if (!(end ? zero_high : zero_low)) continue;
        int found = 0;
        for (int k = 2; k <= 24 && !found; k++) {
            Range delta = range_div(width, range_ratio((__int128)1 << k, 1));
            Range near = end ? (Range){range_sub(hi, delta).low, hi.high} : (Range){lo.low, range_add(lo, delta).high};
            Jet series = jet_eval(u, x, near, 1);
            int slope;
            if (!range_side(series.c[1], &slope)) continue;
            /* Crescente da uno zero a sinistra: positiva dopo; da uno zero a
             * destra: negativa prima. */
            int here = end ? -slope : slope;
            if (*sign && *sign != here) return 0;
            *sign = here;
            if (end) hi = range_sub(hi, delta); else lo = range_add(lo, delta);
            found = 1;
        }
        if (!found) return 0;
    }
    return range_sign(u, x, lo, hi, RIEMANN_SPLITS, sign);
}

/* 30i-2. Divide [p, q] (esatti e con gli intervalli) nelle parti in cui il
 * valore assoluto di f ha un segno fisso, e le mette in piece[], con f senza
 * valore assoluto. Ritorna il numero di parti, 1 se f non ha valori
 * assoluti, 0 se non riesce. */
static int split_pieces(Node *f, int x, Rat p, Rat q, Range low, Range high, Stretch *piece) {
    const Node *bars[MAX_INNER];
    int count = 0;
    collect_abs(f, bars, &count);
    piece[0] = (Stretch){p, q, low, high, f};
    if (count == 0) return 1;
    for (int i = 1; i < count; i++)
        if (!node_equal(bars[i]->a, bars[0]->a)) return 0;
    const Node *u = sample_tree(bars[0]->a, x, 0, 0);

    /* I candidati zeri, poi solo quelli esatti e dentro (p, q). */
    Rat zero[MAX_PIECES];
    Range where[MAX_PIECES];
    int zeros = 0, candidates = 0, xa = atom_var(x);
    Rat candidate[MAX_INNER];
    env_count = 0;
    Rat value = eval(u);
    Poly num, den, part[2];
    if (!failure && rat_polynomials(value, &num, &den) && poly_split(num, xa, part, 1) == 1 && part[1].count)
        candidate[candidates++] = rat_div((Rat){poly_add(poly_const(num_int(0)), part[0], 1), poly_const(num_int(1))}, (Rat){part[1], poly_const(num_int(1))});
    failure = NULL;
    QPoly polynomial;
    if (rat_polynomials(value, &num, &den) && qpoly_from(num, xa, &polynomial) && polynomial.degree >= 2 && polynomial.degree <= MAX_UNIVARIATE) {
        Frac content, root[MAX_UNIVARIATE + 2];
        QPoly whole = qpoly_primitive(polynomial, &content);
        long long c[MAX_UNIVARIATE + 1];
        for (int i = 0; i <= whole.degree; i++) c[i] = whole.c[i].num;
        int roots = failure ? -1 : rational_roots(c, whole.degree, root);
        for (int i = 0; i < roots && candidates < MAX_INNER; i++) candidate[candidates++] = rat_frac(root[i]);
    }
    failure = NULL;
    if (has_trig(u)) {
        Range pi = range_pi();
        for (long long k = (long long)(low.low * 12 / pi.high) - 1; k <= (long long)(high.high * 12 / pi.low) + 1 && candidates < MAX_INNER; k++)
            candidate[candidates++] = rat_mul(rat_frac(frac_make(k, 12)), rat_atom(atom_var(VAR_PI)));
    }
    for (int i = 0; i < candidates; i++) {
        Range r = rat_range(candidate[i]);
        int left, right;
        if (!range_side(range_sub(r, low), &left) || left < 0 || !range_side(range_sub(high, r), &right) || right < 0) continue;
        Rat at = value_at(u, x, candidate[i]);
        if (failure || !poly_vanishes(at.num)) { failure = NULL; continue; }
        int seen = 0;
        for (int j = 0; j < zeros && !seen; j++) seen = poly_vanishes(rat_add(zero[j], candidate[i], 1).num);
        if (seen) continue;
        if (zeros == MAX_PIECES - 1) return 0;
        /* In ordine, inserendo: due zeri diversi hanno intervalli separati
         * (altrimenti non si sa quale viene prima, e si rinuncia). */
        int k = zeros;
        while (k > 0 && range_side(range_sub(where[k - 1], r), &left) && left > 0) { zero[k] = zero[k - 1]; where[k] = where[k - 1]; k--; }
        if (k > 0 && !(range_side(range_sub(r, where[k - 1]), &left) && left > 0)) return 0;
        zero[k] = candidate[i];
        where[k] = r;
        zeros++;
    }

    /* Le parti, il segno di u su ognuna, e f con |u| = u o -u. Anche gli
     * estremi a e b possono essere zeri di u, come 0 per sin x. */
    Rat at_start = value_at(u, x, p), at_end = value_at(u, x, q);
    int zero_start = !failure && poly_vanishes(at_start.num), zero_end = !failure && poly_vanishes(at_end.num);
    failure = NULL;
    Node *plus = (Node *)bars[0]->a, *minus = node_new(N_NEG, (Node *)bars[0]->a, NULL);
    for (int i = 0; i <= zeros; i++) {
        Rat from = i ? zero[i - 1] : p, to = i < zeros ? zero[i] : q;
        Range lo = i ? where[i - 1] : low, hi = i < zeros ? where[i] : high;
        int sign;
        if (!piece_sign(u, x, lo, hi, i > 0 || zero_start, i < zeros || zero_end, &sign)) return 0;
        Node *replacement[MAX_INNER];
        for (int j = 0; j < count; j++) replacement[j] = sign > 0 ? plus : minus;
        piece[i] = (Stretch){from, to, lo, hi, replace_listed(f, bars, replacement, count)};
    }
    return zeros + 1;
}

/* 30j. IL VERDETTO
 *
 * prove_integral() legge l'enunciato (9j), controlla che vi compaiano solo
 * la variabile, e e pi greco, e sceglie la strada: verificare una primitiva
 * (30a, 30b), cercarne una (30c-30h) e verificarla, o calcolare un integrale
 * definito (30i). Le dimostrazioni scritte sono in inglese, come le altre. */

/* Ritorna 1 se in tree compaiono solo la lettera x, e e pi greco (x = 0:
 * solo e e pi greco), e niente somme, successioni o applicazioni. */
static int only_letters(const Node *tree, int x) {
    if (!tree) return 1;
    if (tree->kind == N_VAR && tree->name != x && tree->name != 'e' && tree->name != VAR_PI) return 0;
    if (tree->kind == N_BIGOP || tree->kind == N_SEQ || tree->kind == N_APPLY) return 0;
    return only_letters(tree->a, x) && only_letters(tree->b, x) && only_letters(tree->c, x);
}

/* Scrive nella dimostrazione la verifica di F, già passata da
 * primitive_check(): la derivata con le regole, se non è troppo lunga, e i
 * punti in cui i numeri hanno confermato. Ritorna 0 se la derivata scritta,
 * riletta, non concorda con f nel punto di conferma: un errore nello
 * scriverla. */
static int put_primitive_check(const Node *f, const Node *F, int x, const PrimitiveCheck *check) {
    char written[ANSWER_BYTES];
    proof_add("By the rules of differentiation, ");
    int sound = 1;
    if (node_latex(check->derivative, written, sizeof written) && strlen(written) < 1500) {
        proof_add("$\\frac{d}{d%c}\\left(", x);
        put_node(F, 0);
        proof_add("\\right) = %s$, and the difference from the integrand reduces to $0$ by exact algebra", written);

        /* La derivata scritta, riletta, contro f nel punto di conferma. */
        Node *back = text_tree(written);
        Range at = range_ratio(check->point.num, check->point.den);
        sound = back && numbers_agree(sample_value(sample_tree(back, x, 0, 0), x, at), sample_value(sample_tree(f, x, 0, 0), x, at)) > 0;
    } else {
        proof_add("the derivative of the right side, too long to write here, minus the integrand reduces to $0$ by exact algebra");
    }
    proof_add(". So the derivative of $");
    put_node(F, 0);
    proof_add("$ is the integrand on every open interval where both are defined, and there every antiderivative is this function plus a "
              "constant (two antiderivatives on an interval differ by a constant, by the mean value theorem). \\emph{Check with numbers}: at $%c = "
              "\\frac{%lld}{%lld}$ the derivative read from the Taylor series of the antiderivative, computed with interval arithmetic, agrees "
              "with the integrand.", x, check->point.num, check->point.den);
    if (check->outside) proof_add(" The antiderivative is not defined everywhere the integrand is: for example at $%c = \\frac{%lld}{%lld}$.", x, check->where.num, check->where.den);
    proof_add("\n");
    return sound;
}

/* Il verdetto di una verifica, con il motivo e il punto. */
static Verdict primitive_verdict(const PrimitiveCheck *check, int x) {
    static char where[96];
    Verdict verdict = {check->outcome, 0, 0, 0, check->reason, NULL, NULL, NULL, NULL, NULL};
    if (check->outcome == REFUTED) {
        snprintf(where, sizeof where, "%c = %lld/%lld, dove la derivata della primitiva non è la funzione integranda", x, check->point.num, check->point.den);
        verdict.detail = where;
    }
    return verdict;
}

/* Cerca una primitiva di f in x, la scrive in text (di size byte), la
 * rilegge e la verifica: mette in *check l'esito e ritorna l'albero riletto,
 * o NULL se non la trova o non è verificata. Una primitiva trovata che la
 * verifica smentisce è un errore del programma: unjustified_steps sale. */
static Node *found_primitive(const Node *f, int x, char *text, size_t size, PrimitiveCheck *check) {
    primitive_method = NULL;
    primitive_budget = MAX_PRIMITIVE_CALLS;
    *check = (PrimitiveCheck){NOT_PROVED, "non trovo una primitiva con i metodi del programma", {0, 1}, 0, {0, 1}, NULL};
    if (!primitive_text(f, x, 0, text, size)) { failure = NULL; return NULL; }
    Node *F = text_tree(text);
    if (!F) { unjustified_steps++; check->reason = "la primitiva trovata non si rilegge"; return NULL; }
    *check = primitive_check(f, F, x);
    if (check->outcome == REFUTED) {
        unjustified_steps++;
        check->outcome = NOT_PROVED;
        check->reason = "la primitiva trovata è smentita dalla verifica: un errore del programma";
    }
    if (check->outcome != PROVED) {
        static char reason[256];
        snprintf(reason, sizeof reason, "la primitiva trovata non è verificata: %s", check->reason ? check->reason : "");
        check->reason = reason;
        check->outcome = NOT_PROVED;
        return NULL;
    }
    return F;
}

/* 30j. Il verdetto su un integrale definito di f da lower a upper: se claim
 * non è NULL, "l'integrale vale claim"; altrimenti la richiesta del suo
 * valore. *improper diventa 1 se gli intervalli non mostrano che f è
 * continua su tutto [a, b]: allora l'integrale va trattato come improprio
 * (30k), e il verdetto ritornato non conta. */
static Verdict prove_definite(const Node *f, const Node *lower, const Node *upper, const Node *claim, int x, int *improper) {
    static char answer[ANSWER_BYTES], detail[ANSWER_BYTES + 128];
    char primitive[ANSWER_BYTES];
    Verdict verdict = {NOT_PROVED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};

    /* Gli estremi, esatti e con gli intervalli, nell'ordine. */
    Node *fs = sample_tree(f, x, 0, 0);
    Range a = sample_value(sample_tree(lower, x, 0, 0), x, range_none()), b = sample_value(sample_tree(upper, x, 0, 0), x, range_none());
    int side;
    if (!range_side(range_sub(b, a), &side)) { verdict.reason = "non riesco a stabilire quale dei due estremi è il più piccolo"; return verdict; }
    int flip = side < 0;
    Range low = flip ? b : a, high = flip ? a : b;
    Range claimed = claim ? sample_value(sample_tree(claim, x, 0, 0), x, range_none()) : range_none();

    /* L'involucro di Riemann, senza F: basta per il FALSO. */
    Enclosure plain = riemann_enclosure(fs, NULL, x, low, high, 16 * RIEMANN_PIECES);
    if (plain.broken) { unjustified_steps++; verdict.reason = "due stime garantite dell'integrale non si toccano: un errore del programma"; return verdict; }
    if (!plain.defined) {
        verdict.reason = "non riesco a stabilire che la funzione integranda sia continua su tutto l'intervallo di integrazione";
        *improper = 1;
        return verdict;
    }
    Range integral = flip ? range_neg(plain.integral) : plain.integral;
    if (claim && range_known(claimed) && (claimed.high < integral.low || claimed.low > integral.high)) {
        snprintf(detail, sizeof detail, "il valore scritto è fuori da [%.16g, %.16g], che contiene l'integrale", integral.low, integral.high);
        proof_add("\\textbf{Proof that the statement is false.} The integrand is continuous on the interval of integration: interval arithmetic on "
                  "each of its pieces keeps every denominator away from zero and every logarithm and root inside its domain. Riemann sums with interval "
                  "arithmetic then enclose the integral in $");
        put_range(integral);
        proof_add("$, and the stated value lies outside, in $");
        put_range(claimed);
        proof_add("$.");
        verdict.outcome = REFUTED;
        verdict.detail = detail;
        verdict.proof = proof_text;
        return verdict;
    }

    /* Le parti (30i-2), ognuna con una primitiva verificata, e la somma dei
     * F(q) - F(p): con i conti esatti, e con gli intervalli per il
     * controllo. Gli estremi esatti vanno nell'ordine di low e high. */
    env_count = 0;
    Rat from = eval(flip ? upper : lower);
    Rat to = eval(flip ? lower : upper);
    if (failure) { verdict.reason = failure; failure = NULL; return verdict; }
    Stretch piece[MAX_PIECES];
    Node *F[MAX_PIECES];
    PrimitiveCheck check[MAX_PIECES];
    int pieces = split_pieces((Node *)f, x, from, to, low, high, piece);
    failure = NULL;
    if (pieces == 0) { verdict.reason = "non riesco a dividere l'intervallo nelle parti in cui un valore assoluto ha segno costante"; return verdict; }
    Rat exact = rat_int(0);
    Range by_primitive = {0, 0};
    for (int i = 0; i < pieces; i++) {
        F[i] = found_primitive(piece[i].f, x, primitive, sizeof primitive, &check[i]);
        if (!F[i]) { verdict.reason = check[i].reason; return verdict; }
        Node *Fs = sample_tree(F[i], x, 0, 0);
        if (!riemann_enclosure(sample_tree(piece[i].f, x, 0, 0), Fs, x, piece[i].low, piece[i].high, 16 * RIEMANN_PIECES).defined) {
            verdict.reason = "la primitiva trovata non è definita su tutto l'intervallo di integrazione";
            *improper = pieces == 1;
            return verdict;
        }
        Rat at_end = value_at(F[i], x, piece[i].q);
        Rat at_start = value_at(F[i], x, piece[i].p);
        exact = rat_add(exact, rat_add(at_end, at_start, 1), 0);
        by_primitive = range_add(by_primitive, range_sub(sample_value(Fs, x, piece[i].high), sample_value(Fs, x, piece[i].low)));
        if (failure) { verdict.reason = failure; failure = NULL; return verdict; }
    }
    if (flip) {
        exact = rat_add(rat_int(0), exact, 1);
        by_primitive = range_neg(by_primitive);
    }

    /* Il controllo indipendente: la somma dei F(q) - F(p), con gli
     * intervalli, dentro l'involucro di Riemann. */
    if (!range_known(by_primitive) || by_primitive.high < integral.low || by_primitive.low > integral.high) {
        unjustified_steps++;
        verdict.reason = "F(b) - F(a) non sta nell'involucro di Riemann dell'integrale: un errore del programma";
        return verdict;
    }
    double size = integral.high > -integral.low ? integral.high : -integral.low;
    if (integral.high - integral.low > 1e-3 * (1 + size)) { verdict.reason = "le somme di Riemann con gli intervalli non sono abbastanza precise per il controllo"; return verdict; }

    /* Il valore: da confrontare con quello scritto, o da scrivere. */
    const char *value_text = NULL;
    const Node *value = claim;
    if (claim) {
        env_count = 0;
        Rat gap = rat_add(exact, eval(claim), 1);
        if (failure || !poly_vanishes(gap.num)) {
            failure = NULL;
            verdict.reason = "F(b) - F(a) e il valore scritto non si riducono allo stesso numero con i conti esatti";
            return verdict;
        }
    } else {
        /* Il numero, scritto e riletto come ogni risultato: semplificato
         * dai conti esatti se si sa scrivere, altrimenti F(b) - F(a) così
         * com'è. */
        Node *back = NULL;
        if (rat_latex(exact, answer, sizeof answer)) back = text_tree(answer);
        if (!back && pieces == 1 && node_latex(node_new(N_SUB, node_replace(F[0], x, (Node *)upper), node_replace(F[0], x, (Node *)lower)), answer, sizeof answer))
            back = text_tree(answer);
        if (!back) { verdict.reason = "non riesco a scrivere il valore dell'integrale"; return verdict; }
        env_count = 0;
        Rat gap = rat_add(exact, eval(back), 1);
        Range reread = sample_value(sample_tree(back, x, 0, 0), x, range_none());
        if (failure || !poly_vanishes(gap.num) || !range_known(reread) || reread.high < integral.low || reread.low > integral.high) {
            failure = NULL;
            unjustified_steps++;
            verdict.reason = "il valore scritto, riletto, non è quello calcolato";
            return verdict;
        }
        value_text = answer;
        value = back;
    }

    /* La dimostrazione: le parti, se sono più d'una, poi ogni primitiva. */
    proof_add("\\textbf{Proof.} By the fundamental theorem of calculus: if $f$ is continuous on $[p, q]$ and $F' = f$ on an open interval "
              "containing $[p, q]$, the integral from $p$ to $q$ is $F(q) - F(p)$.");
    if (pieces > 1)
        proof_add(" The absolute value in the integrand vanishes at %d point%s of the interval: each is an exact zero, and between two consecutive ones "
                  "its argument has a constant sign (monotone near each zero, by its derivative computed with interval arithmetic, and of certain sign "
                  "elsewhere). On each piece the absolute value is its argument or its opposite, and the integral is the sum over the pieces.",
                  pieces - 1, pieces > 2 ? "s" : "");
    for (int i = 0; i < pieces; i++) {
        proof_add(pieces > 1 ? "\n\nOn the piece number %d, " : " ", i + 1);
        proof_add("$F = ");
        put_node(F[i], 0);
        proof_add("$, found by the search for an antiderivative. ");
        if (!put_primitive_check(piece[i].f, F[i], x, &check[i])) {
            unjustified_steps++;
            verdict.reason = "la derivata scritta nella dimostrazione, riletta, non è confermata";
            return verdict;
        }
    }
    proof_add("Interval arithmetic on each part of the interval of integration keeps every denominator of the integrand and of the antiderivative "
              "away from zero, and every logarithm and root inside its domain: the antiderivative is analytic on a neighbourhood of every point "
              "of it, and the integrand continuous. Hence the integral is the sum of the $F(q) - F(p)$");
    if (value_text) proof_add(", that is $%s$", value_text);
    proof_add(". \\emph{Check with numbers}: Riemann sums with interval arithmetic, which use neither the antiderivatives nor exact algebra, "
              "enclose the integral in $");
    put_range(integral);
    proof_add("$, and the sum lies there. $\\Box$");
    verdict.proof = proof_text;
    verdict.reason = NULL;
    if (value_text) {
        verdict.outcome = SOLVED;
        verdict.method = "con il teorema fondamentale del calcolo";
        verdict.detail = value_text;
    } else {
        verdict.outcome = PROVED;
        verdict.method = "con il teorema fondamentale del calcolo, e l'involucro di Riemann come controllo";
    }

    /* 30cert. Il certificato di un integrale ha una primitiva sola: con le
     * parti di un valore assoluto (30i-2) manca. Il verificatore ricontrolla
     * F' = f, che f e F siano definite su tutto l'intervallo, e il valore. */
    if (pieces == 1) calculus_certify(&verdict, calculus_certificate("integral", x, NULL, F[0], f, lower, upper, value), NULL, x);
    else verdict.reason = "il certificato di un integrale ha una primitiva sola, e qui un valore assoluto divide l'intervallo in parti";
    return verdict;
}

/* 30k. GLI INTEGRALI IMPROPRI
 *
 * A che cosa serve. "\int_{1}^{+\infty} \frac{dx}{x^{2}} = 1",
 * "\int_{0}^{\pi/2} \tan x \, dx = +\infty", "\int_{0}^{1} \frac{dx}{\sqrt{x}}",
 * "\int_{1}^{+\infty} \sin^{2}\frac{1}{x} \, dx \in \mathbb{R}": un estremo
 * infinito, o una funzione che vicino a un estremo non è limitata.
 *
 * LA DEFINIZIONE
 *
 * Sia f continua sull'intervallo aperto (a, b), con a un numero o -\infty e b
 * un numero o +\infty. Per un c in (a, b) si guardano i due limiti
 *
 *     lim_{q -> b^-} \int_c^q f      e      lim_{p -> a^+} \int_p^c f.
 *
 * Se esistono finiti, l'integrale improprio converge e vale la loro somma;
 * cambiare c sposta un pezzo finito da un limite all'altro, e la somma non
 * cambia. Se uno è +\infty e l'altro finito o +\infty, l'integrale vale
 * +\infty (diverge); lo stesso per -\infty. Altrimenti (un limite che non
 * esiste, o +\infty da una parte e -\infty dall'altra) l'integrale non
 * converge e non vale un infinito. Se f non è definita in un punto c
 * interno, (a, b) si divide in c, e l'integrale converge se converge su
 * ogni parte. Se f è continua anche negli estremi, che sono numeri, la
 * definizione dà l'integrale di sempre (la funzione integrale è continua):
 * la estende, non la cambia. Per questo un integrale definito che gli
 * intervalli non sanno dire continuo su tutto [a, b] (30i) viene trattato
 * qui.
 *
 * IL TEOREMA E IL METODO (30k-1 ... 30k-4)
 *
 * Se F è derivabile su (a, b) con F' = f, per ogni [p, q] dentro (a, b) il
 * teorema fondamentale dà \int_p^q f = F(q) - F(p), e quindi l'integrale
 * improprio è lim_{x -> b^-} F(x) - lim_{x -> a^+} F(x), sui numeri reali
 * estesi, con le regole della definizione. Si controllano, ognuno con il
 * suo metodo:
 *
 *   30k-1. che f sia continua su (a, b), e F derivabile: domain_conditions()
 *          raccoglie le condizioni di esistenza di f, di F e della derivata
 *          di F scritta dalle regole (divisori diversi da zero, argomenti dei
 *          logaritmi positivi, radicandi non negativi, coseni diversi da zero
 *          sotto una tangente), e la tabella dei segni (18p), con le sue
 *          verifiche, decide l'enunciato "per ogni x con a < x < b valgono".
 *          Una funzione elementare è continua dove è definita; e dove la
 *          formula della derivata ha un valore F è derivabile e quella è la
 *          sua derivata (capitolo 27, "Dove valgono le formule"). Se la
 *          tabella trova un punto c in cui una condizione non vale,
 *          l'intervallo si divide in c e si ricomincia, fino a
 *          MAX_IMPROPER_PIECES parti;
 *   30k-2. che F' = f: primitive_check(), come per le primitive (30a, 30b);
 *   30k-3. i limiti di F agli estremi di ogni parte: il capitolo 29, con la
 *          scala delle crescite (29k) e i suoi controlli (29i, 29j), come
 *          richieste \lim_{x \to b^{-}} F, scritte e rilette;
 *   30k-4. il controllo indipendente, con i numeri: su intervalli compatti
 *          [p_k, q_k] che si allargano verso gli estremi (q_k = b - 2^{-k}
 *          (b - c), oppure c + 2^{k-1} se b = +\infty), l'involucro di
 *          Riemann di 30i chiude \int_{p_k}^{q_k} f senza usare F, e
 *          F(q_k) - F(p_k), calcolato con gli intervalli, deve starci dentro.
 *          Gli intervalli si fermano dove non sanno più calcolare f (un
 *          esponenziale che esce dai numeri della macchina vicino a
 *          +\infty); ma se su uno di essi f non si chiude pur calcolandosi
 *          nei suoi due estremi, lì dentro c'è forse un punto in cui f non è
 *          definita, sfuggito a 30k-1, e il controllo smentisce.
 *          Che cosa garantisce: che F sia una primitiva su ogni compatto
 *          guardato, per una strada che non usa né le regole di derivazione
 *          né i conti esatti; un F sbagliato, o una divisione sfuggita al
 *          primo controllo, lo fa uscire. Che cosa no: i limiti agli estremi,
 *          che un numero finito di intervalli non vede; quelli li ricontrolla
 *          29i, e la convergenza la ricontrolla il confronto (30l) quando sa
 *          deciderla: se i due metodi non sono d'accordo il verdetto è NON
 *          DIMOSTRATO, e il passo si conta tra quelli non giustificati.
 *
 * Perché i capitoli si parlano con dei testi. La tabella dei segni e i
 * limiti ripartono da zero, e svuotano l'arena: si chiedono con enunciati
 * scritti in LaTeX (ask_method()), come farebbe un utente, e ciò che
 * rispondono (un controesempio, un limite) è un testo che si rilegge. Gli
 * alberi della funzione e della primitiva si rileggono dai loro testi
 * quando servono di nuovo. */

#define MAX_IMPROPER_PIECES 4  /* parti in cui un integrale improprio si divide nei punti interni (30k-1) */
#define IMPROPER_STEPS 12      /* intervalli compatti del controllo con i numeri (30k-4) */

/* Un estremo di una parte di un integrale improprio, o il valore di un
 * limite: un infinito, oppure un numero scritto in LaTeX. */
typedef struct {
    int infinite;              /* +1 per +\infty, -1 per -\infty, 0 per un numero */
    char text[ANSWER_BYTES];   /* il numero, se infinite è 0: si rilegge con il lettore */
} EndText;

/* Ciò che si sa di un integrale improprio, o di un suo estremo. */
typedef enum {
    IMPROPER_UNKNOWN,     /* non si sa */
    IMPROPER_FINITE,      /* converge */
    IMPROPER_PLUS,        /* vale +\infty */
    IMPROPER_MINUS,       /* vale -\infty */
    IMPROPER_NEITHER,     /* non converge, e non vale un infinito */
    IMPROPER_DIVERGENT    /* non converge; se valga un infinito non si sa */
} ImproperResult;

/* Gli estremi delle parti, da sinistra a destra: la parte i va da
 * improper_point[i] a improper_point[i + 1]. */
static EndText improper_point[MAX_IMPROPER_PIECES + 1];
static int improper_pieces;

/* Ripartenza da zero per un enunciato sugli integrali: l'arena, la tabella
 * degli atomi e le variabili dei conti; non il testo della dimostrazione. */
static void integral_reset(void) {
    arena_used = arena_keep;
    atom_count = base_poly_count = atan_count = 0;
    failure = NULL;
    env_count = point_count = 0;
    conditions_on = 0;
    induction_var = 0;
    default_base = domain_floor = 0;
}

/* LE CONDIZIONI DI ESISTENZA (30k-1) */

/* Ritorna 1 se c, che non contiene x, ha un valore, e mette in *value un
 * intervallo che lo contiene. */
static int constant_value(const Node *c, int x, Range *value) {
    *value = sample_value(sample_tree(c, x, 0, 0), x, range_none());
    return range_known(*value);
}

/* Ritorna 1 se c, che non contiene x, è un intero, e lo mette in *n. */
static int constant_integer(const Node *c, int x, long long *n) {
    if (node_has_variable(c, x)) return 0;
    const char *saved = failure;
    env_count = 0;
    Rat r = eval(c);
    Num v;
    int whole = !failure && rat_number(r, &v) && v.im.num == 0 && v.re.den == 1;
    failure = saved;
    if (whole) *n = v.re.num;
    return whole;
}

/* Aggiunge alla congiunzione text la condizione "\left(u\right) relation",
 * se non c'è già. Ritorna 0 se non ci sta. */
static int condition_add(const Node *u, const char *relation, char *text, size_t size) {
    char written[ANSWER_BYTES], piece[ANSWER_BYTES + 32];
    if (!node_latex(u, written, sizeof written)) return 0;
    snprintf(piece, sizeof piece, "\\left(%s\\right) %s", written, relation);
    if (strstr(text, piece)) return 1;
    if (strlen(text) + strlen(piece) + 8 >= size) return 0;
    text_add(text, size, "%s%s", text[0] ? " \\land " : "", piece);
    return 1;
}

/* La condizione u != 0, ridotta dove si sa: un prodotto è zero se lo è un
 * fattore, una potenza o una radice se lo è la base, c^v (con c > 0) e e^v
 * mai. Chi chiama ha già posto le condizioni di esistenza di u. Ritorna 0
 * come condition_add(), o se u è una costante che non si sa diversa da
 * zero. */
static int condition_nonzero(const Node *u, int x, char *text, size_t size) {
    Range value;
    long long n;
    int side;
    if (!node_has_variable(u, x)) return constant_value(u, x, &value) && range_side(value, &side);
    switch (u->kind) {
    case N_NEG:
        return condition_nonzero(u->a, x, text, size);
    case N_MUL:
        return condition_nonzero(u->a, x, text, size) && condition_nonzero(u->b, x, text, size);
    case N_DIV:
        return condition_nonzero(u->a, x, text, size);
    case N_POW:
        /* c^v e u^v = e^{v ln u} hanno la base positiva; u^0 = 1, e u^{-n}
         * ha già u != 0 tra le condizioni. */
        if (!node_has_variable(u->a, x) || node_has_variable(u->b, x)) return 1;
        if (constant_integer(u->b, x, &n) && n <= 0) return 1;
        return condition_nonzero(u->a, x, text, size);
    case N_CALL:
        if (u->op == FN_ROOT || u->op == FN_ABS) return condition_nonzero(u->a, x, text, size);
        break;
    default:
        break;
    }
    return condition_add(u, "\\ne 0", text, size);
}

/* La condizione u > 0, ridotta come in condition_nonzero(): |v| > 0 se
 * v != 0, e c^v > 0 sempre. */
static int condition_positive(const Node *u, int x, char *text, size_t size) {
    Range value;
    int side;
    if (!node_has_variable(u, x)) return constant_value(u, x, &value) && range_side(value, &side) && side > 0;
    if (u->kind == N_CALL && u->op == FN_ABS) return condition_nonzero(u->a, x, text, size);
    if (u->kind == N_POW && !node_has_variable(u->a, x)) return 1;
    return condition_add(u, "> 0", text, size);
}

/* La condizione u >= 0: vale da sé per |v|, c^v e le potenze pari. */
static int condition_nonnegative(const Node *u, int x, char *text, size_t size) {
    long long n;
    if (u->kind == N_CALL && u->op == FN_ABS) return 1;
    if (u->kind == N_POW && (!node_has_variable(u->a, x) || (constant_integer(u->b, x, &n) && n % 2 == 0))) return 1;
    return condition_add(u, "\\ge 0", text, size);
}

/* 30k-1. Aggiunge alla congiunzione text le condizioni perché tree, nella
 * variabile x, sia definita: divisori diversi da zero, argomenti dei
 * logaritmi e basi delle potenze con un esponente non intero (o con x
 * nell'esponente: u^v = e^{v ln u}) positivi, radicandi di indice pari non
 * negativi, coseni diversi da zero sotto una tangente (seni sotto una
 * cotangente), |u| <= 1 sotto un arcoseno. Una parte senza x deve avere un
 * valore. Sono le stesse convenzioni del resto del programma (29f, 29h).
 * Ritorna 0 se tree contiene ciò che qui non si tratta (fattoriali,
 * somme con \sum, applicazioni), o se il testo non ci sta. */
static int domain_conditions(const Node *tree, int x, char *text, size_t size) {
    Range value;
    long long n;
    int side;
    if (!node_has_variable(tree, x)) return constant_value(tree, x, &value);
    switch (tree->kind) {
    case N_VAR:
        return 1;
    case N_NEG:
        return domain_conditions(tree->a, x, text, size);
    case N_ADD: case N_SUB: case N_MUL:
        return domain_conditions(tree->a, x, text, size) && domain_conditions(tree->b, x, text, size);
    case N_DIV:
        return domain_conditions(tree->a, x, text, size) && domain_conditions(tree->b, x, text, size) && condition_nonzero(tree->b, x, text, size);
    case N_POW:
        if (!domain_conditions(tree->a, x, text, size) || !domain_conditions(tree->b, x, text, size)) return 0;
        if (tree->a->kind == N_VAR && tree->a->name == 'e') return 1;
        if (constant_integer(tree->b, x, &n)) return n >= 0 || condition_nonzero(tree->a, x, text, size);
        return condition_positive(tree->a, x, text, size);
    case N_CALL:
        if (!domain_conditions(tree->a, x, text, size)) return 0;
        switch ((Function)tree->op) {
        case FN_SIN: case FN_COS: case FN_ARCTAN: case FN_ARCCOT: case FN_ABS:
            return 1;
        case FN_TAN:
            return condition_nonzero(node_call(FN_COS, tree->a, NULL), x, text, size);
        case FN_COT:
            return condition_nonzero(node_call(FN_SIN, tree->a, NULL), x, text, size);
        case FN_LN:
            return condition_positive(tree->a, x, text, size);
        case FN_LOG:
            /* La base è un numero positivo diverso da 1. */
            if (!tree->b || node_has_variable(tree->b, x) || !constant_value(tree->b, x, &value) || !range_side(value, &side) || side < 0 ||
                !range_side(range_sub(value, range_ratio(1, 1)), &side))
                return 0;
            return condition_positive(tree->a, x, text, size);
        case FN_ROOT:
            if (!constant_integer(tree->b, x, &n) || n < 2) return 0;
            return n % 2 || condition_nonnegative(tree->a, x, text, size);
        case FN_ARCSIN: case FN_ARCCOS:
            return condition_add(tree->a, "^{2} \\le 1", text, size);
        default:
            return 0;
        }
    default:
        return 0;
    }
}

/* I TESTI DEGLI ESTREMI */

/* Scrive in text l'estremo e: +\infty, -\infty o il numero. */
static void end_latex(const EndText *e, char *text, size_t size) {
    snprintf(text, size, "%s", e->infinite > 0 ? "+\\infty" : e->infinite < 0 ? "-\\infty" : e->text);
}

/* Mette in *value l'intervallo del numero dell'estremo e (finito). Ritorna 0
 * se il testo non si rilegge o non ha un valore. Usa l'arena. */
static int end_range(const EndText *e, int x, Range *value) {
    Node *tree = text_tree(e->text);
    return tree && constant_value(tree, x, value);
}

/* Ritorna 1 se l'estremo c sta di sicuro tra p e q, che possono essere
 * infiniti. */
static int end_between(const EndText *p, const EndText *c, const EndText *q, int x) {
    Range low, middle, high;
    int side;
    if (c->infinite || !end_range(c, x, &middle)) return 0;
    if (!p->infinite && !(end_range(p, x, &low) && range_side(range_sub(middle, low), &side) && side > 0)) return 0;
    if (!q->infinite && !(end_range(q, x, &high) && range_side(range_sub(high, middle), &side) && side > 0)) return 0;
    return 1;
}

/* 30k-1. Chiede alla tabella dei segni se le condizioni conditions valgono
 * su ogni parte (improper_point[]), e divide una parte nel punto in cui la
 * tabella le smentisce. Ritorna 1 se alla fine valgono su ogni parte, 0 se
 * non si sa. La dimostrazione della tabella entra nel testo. */
static int improper_domain(const char *conditions, int x) {
    static char question[MAX_FORMULA], low[ANSWER_BYTES], high[ANSWER_BYTES];
    if (!conditions[0]) {
        proof_add("Every operation in the integrand is defined for every real number, so it is continuous everywhere.\n");
        return 1;
    }
    for (int i = 0; i < improper_pieces;) {
        const EndText *p = &improper_point[i], *q = &improper_point[i + 1];
        end_latex(p, low, sizeof low);
        end_latex(q, high, sizeof high);
        int wanted;
        if (p->infinite && q->infinite) wanted = snprintf(question, sizeof question, "\\forall %c \\in \\mathbb{R}\\ (%s)", x, conditions);
        else if (p->infinite) wanted = snprintf(question, sizeof question, "\\forall %c \\in \\mathbb{R}\\ (%c < %s \\implies %s)", x, x, high, conditions);
        else if (q->infinite) wanted = snprintf(question, sizeof question, "\\forall %c \\in \\mathbb{R}\\ (%s < %c \\implies %s)", x, low, x, conditions);
        else wanted = snprintf(question, sizeof question, "\\forall %c \\in \\mathbb{R}\\ (%s < %c \\land %c < %s \\implies %s)", x, low, x, x, high, conditions);
        if (wanted < 0 || (size_t)wanted >= sizeof question) return 0;
        /* Si scrive la domanda intera, con l'implicazione: la tabella che
         * segue ha righe anche fuori dall'intervallo, dove l'implicazione
         * vale perché la sua ipotesi è falsa. Con le sole condizioni, una riga
         * come "x = 0: la condizione vale" sembrava dire x \ne 0 in x = 0. */
        proof_add("\n\\emph{Where the functions are defined}, on $(%s, %s)$: the conditions $%s$ must hold there, that is $%s$; "
                  "outside the interval the implication holds because its hypothesis is false.\n", low, high, conditions, question);
        Verdict table = ask_method(prove_quantified, question, "The sign table, too long to be written here, shows that the conditions hold on every row.", 1);
        proof_add("\n");
        if (table.outcome == PROVED) { i++; continue; }

        /* Smentite in un punto c: si divide la parte in c. */
        const char *value = table.outcome == REFUTED && table.detail ? strstr(table.detail, "= ") : NULL;
        if (!value || improper_pieces == MAX_IMPROPER_PIECES) return 0;
        EndText c = {0, ""};
        snprintf(c.text, sizeof c.text, "%s", value + 2);
        if (!end_between(p, &c, q, x)) return 0;
        for (int k = improper_pieces; k > i; k--) improper_point[k + 1] = improper_point[k];
        improper_point[i + 1] = c;
        improper_pieces++;
        proof_add("\nThe sign table finds a point where a condition fails, $%c = %s$: the interval is split there, and each part is improper "
                  "at that end.\n", x, c.text);
    }
    return 1;
}

/* 30k-3. Il limite della funzione scritta in function quando x tende
 * all'estremo end, da destra se side è +1 e da sinistra se è -1 (per un
 * estremo infinito side non conta), chiesto al capitolo 29: mette in *out
 * l'infinito o il valore scritto, e ritorna 1 se il limite è calcolato. La
 * dimostrazione del limite entra nel testo, dopo intro. */
static int improper_limit(const char *function, int x, const EndText *end, int side, const char *intro, EndText *out) {
    static char question[MAX_FORMULA];
    int wanted = end->infinite ? snprintf(question, sizeof question, "\\lim_{%c \\to %s} %s", x, end->infinite > 0 ? "+\\infty" : "-\\infty", function)
                               : snprintf(question, sizeof question, "\\lim_{%c \\to %s^{%c}} %s", x, end->text, side > 0 ? '+' : '-', function);
    if (wanted < 0 || (size_t)wanted >= sizeof question) return 0;
    proof_add("%s", intro);
    Verdict limit = ask_method(prove_limit, question, "The limit, computed with the expansions of chapter 29, is the one written here.", 1);
    proof_add("\n");
    if (limit.outcome != SOLVED || !limit.detail) return 0;
    const char *value = NULL;
    for (const char *s = strstr(limit.detail, " = "); s; s = strstr(s + 1, " = ")) value = s + 3;
    if (!value) return 0;
    out->infinite = infinity_text(value, value + strlen(value));
    if (out->infinite == 2) return 0;
    snprintf(out->text, sizeof out->text, "%s", value);
    return 1;
}

/* 30l. IL CONFRONTO
 *
 * Quando non si trova una primitiva, la convergenza si decide dal
 * comportamento di f vicino a ogni estremo. Con t -> 0^{+} la lettera di 29a
 * (t = b - x vicino a un estremo b, t = 1/|x| all'infinito) e L = ln(1/t),
 * sia g = t^{e} L^{d}, positiva vicino all'estremo. I teoremi:
 *
 *   (C1) confronto asintotico: se f / g -> c con c != 0 finito, allora f ha
 *        il segno di c vicino all'estremo, |f| sta tra |c| g / 2 e 2 |c| g,
 *        e \int f converge se e solo se converge \int g; se \int g diverge,
 *        \int f vale \infty con il segno di c;
 *   (C2) se f / g -> 0 e \int g converge, allora |f| <= g vicino
 *        all'estremo, e \int f converge (assolutamente);
 *   (C3) se f / g -> \pm\infty e \int g diverge, allora f ha il segno
 *        dell'infinito e |f| >= g vicino all'estremo: \int f vale \infty con
 *        quel segno.
 *
 * E la scala di g (con s = ln(1/t), \int t^{e} L^{d} dt = \int e^{-(e + 1) s}
 * s^{d} ds verso s = +\infty, o con x = 1/t all'infinito):
 *
 *   - vicino a un estremo b che è un numero, \int (b - x)^{e} L^{d} dx
 *     converge se e solo se e > -1, oppure e = -1 e d < -1;
 *   - all'infinito, \int |x|^{-e} (\ln|x|)^{d} dx converge se e solo se
 *     e > 1, oppure e = 1 e d < -1.
 *
 * La g viene dal termine principale di f (29m, limit_leading()), che è un
 * conto del capitolo 29 confermato dal suo controllo con i numeri (29i):
 * f = c t^{e} L^{d} (1 + o(1)) con c != 0 dice proprio f / g -> c con
 * g = t^{e} L^{d}, ed è (C1). Se f ha un fattore e^{G} con G -> -\infty, f
 * è più piccola di ogni potenza (29k-b): f / g -> 0 con g = t^{-1/2} (o
 * x^{-2} all'infinito), ed è (C2); con G -> +\infty f / g -> \pm\infty con
 * g = t^{-1} (o 1), ed è (C3). Se della serie si conosce solo il resto,
 * f = O(t^{e}) (\frac{\sin x}{x^{2}} all'infinito è O(t^{2})), allora
 * |f| <= C g con g = t^{e}: è (C2), e decide solo quando \int g converge.
 * Del coefficiente c servono il segno e che non sia zero, che il conto
 * decide in modo esatto. I casi in cui f oscilla senza tendere a zero
 * abbastanza in fretta (\cos x all'infinito) restano non decisi. */

/* 30l. Il confronto all'estremo end di una parte (side +1 se è l'estremo
 * sinistro, a cui si arriva da destra, -1 se è il destro) per la funzione
 * scritta in function: ritorna IMPROPER_FINITE se l'integrale converge
 * vicino a end, IMPROPER_PLUS o IMPROPER_MINUS se vale un infinito,
 * IMPROPER_UNKNOWN se non si sa. Con proof scrive il ragionamento. */
static ImproperResult improper_compare(const char *function, int x, const EndText *end, int side, int proof) {
    static char question[MAX_FORMULA], t[ANSWER_BYTES], ell[ANSWER_BYTES], g[2 * ANSWER_BYTES];
    char e_text[64] = "", d_text[64] = "", where[ANSWER_BYTES];
    int wanted = end->infinite ? snprintf(question, sizeof question, "\\lim_{%c \\to %s} %s", x, end->infinite > 0 ? "+\\infty" : "-\\infty", function)
                               : snprintf(question, sizeof question, "\\lim_{%c \\to %s^{%c}} %s", x, end->text, side > 0 ? '+' : '-', function);
    if (wanted < 0 || (size_t)wanted >= sizeof question) return IMPROPER_UNKNOWN;
    LeadingTerm lead = limit_leading(question);
    if (!lead.found) return IMPROPER_UNKNOWN;

    /* La g: t^{e} L^{d} per (C1), oppure quella di (C2) o di (C3) con il
     * fattore e^{G}; e la scala, se il suo integrale converge. */
    int finite_end = !end->infinite;
    Frac e = lead.growth > 0 ? frac_int(finite_end ? -1 : 0) : lead.growth < 0 ? (finite_end ? (Frac){-1, 2} : frac_int(2)) : lead.e;
    Frac d = lead.growth ? frac_int(0) : lead.d;
    int g_converges = finite_end ? (frac_cmp(e, frac_int(-1)) > 0 || (frac_cmp(e, frac_int(-1)) == 0 && frac_cmp(d, frac_int(-1)) < 0))
                                 : (frac_cmp(e, frac_int(1)) > 0 || (frac_cmp(e, frac_int(1)) == 0 && frac_cmp(d, frac_int(-1)) < 0));
    ImproperResult result = lead.growth < 0 || (!lead.growth && g_converges) ? IMPROPER_FINITE : lead.sign > 0 ? IMPROPER_PLUS : IMPROPER_MINUS;

    /* Con il solo resto, |f| <= C g: dice che converge se converge \int g
     * (C2), e niente se diverge. */
    if (lead.bound && !g_converges) return IMPROPER_UNKNOWN;
    if (!proof) return result;

    /* La dimostrazione: t, positiva e che tende a 0, L = ln(1/t), la g, e
     * il teorema usato. */
    if (end->infinite) {
        snprintf(t, sizeof t, end->infinite > 0 ? "\\frac{1}{%c}" : "\\left(-\\frac{1}{%c}\\right)", x);
        snprintf(ell, sizeof ell, end->infinite > 0 ? "\\ln %c" : "\\ln(-%c)", x);
    } else {
        if (side < 0) snprintf(t, sizeof t, "\\left(%s - %c\\right)", end->text, x);
        else snprintf(t, sizeof t, "\\left(%c - \\left(%s\\right)\\right)", x, end->text);
        snprintf(ell, sizeof ell, "-\\ln%s", t);
    }
    frac_latex(e, e_text, sizeof e_text);
    frac_latex(d, d_text, sizeof d_text);
    g[0] = 0;
    if (e.num) text_add(g, sizeof g, "\\left(%s\\right)^{%s}", t, e_text);
    if (d.num) text_add(g, sizeof g, "%s\\left(%s\\right)^{%s}", g[0] ? " " : "", ell, d_text);
    if (!g[0]) text_add(g, sizeof g, "1");
    end_latex(end, where, sizeof where);
    if (failure) { failure = NULL; return IMPROPER_UNKNOWN; }
    proof_add("\n\\emph{Comparison as $%c \\to %s%s$}, with $g = %s$, positive near the end. The expansions of the limits (with their check with "
              "numbers) give %s. The integral of $g$ %s near this end (%s), so, by %s, the integral of the integrand %s there.\n", x, where,
              finite_end ? side > 0 ? "^{+}" : "^{-}" : "", g,
              lead.growth < 0 ? "an integrand smaller than every power, so $f / g \\to 0$"
              : lead.growth > 0 ? (lead.sign > 0 ? "an integrand larger than every power, so $f / g \\to +\\infty$"
                                                 : "an integrand larger than every power in absolute value, so $f / g \\to -\\infty$")
              : lead.bound ? "only a bound, $f = O(g)$, that is $|f| \\le C g$ near the end"
              : lead.sign > 0 ? "$f / g \\to c$ with $c > 0$" : "$f / g \\to c$ with $c < 0$",
              g_converges ? "converges" : "diverges",
              finite_end ? "$\\int (b - x)^{e} \\left(\\ln\\frac{1}{b - x}\\right)^{d} dx$ converges near $b$ if and only if $e > -1$, or $e = -1$ and $d < -1$"
                         : "$\\int |x|^{-e} \\left(\\ln |x|\\right)^{d} dx$ converges at infinity if and only if $e > 1$, or $e = 1$ and $d < -1$",
              lead.growth > 0 ? "comparison ($|f| \\ge g$ near the end, with the sign of $f$)"
              : lead.growth < 0 || lead.bound ? "comparison ($|f| \\le C g$ near the end: the integral converges absolutely)"
                                              : "asymptotic comparison",
              result == IMPROPER_FINITE ? "converges" : result == IMPROPER_PLUS ? "is $+\\infty$" : "is $-\\infty$");
    return result;
}

/* Ritorna ciò che dicono di un integrale improprio i risultati result[] dei
 * suoi count estremi (30l): converge se converge vicino a ogni estremo; un
 * infinito, se tutti quelli che divergono hanno lo stesso segno e degli
 * altri si sa che convergono; nessuno dei due, se due divergono con segni
 * opposti (+\infty - \infty non ha un valore). */
static ImproperResult improper_combine(const ImproperResult *result, int count) {
    int unknown = 0, plus = 0, minus = 0;
    for (int i = 0; i < count; i++) {
        unknown |= result[i] == IMPROPER_UNKNOWN;
        plus |= result[i] == IMPROPER_PLUS;
        minus |= result[i] == IMPROPER_MINUS;
    }
    if (plus && minus) return IMPROPER_NEITHER;
    if (unknown) return plus || minus ? IMPROPER_DIVERGENT : IMPROPER_UNKNOWN;
    return plus ? IMPROPER_PLUS : minus ? IMPROPER_MINUS : IMPROPER_FINITE;
}

/* 30k-3. I limiti di F (scritta in function) agli estremi di ogni parte, in
 * from[] (da destra dell'estremo sinistro) e to[] (da sinistra del destro).
 * Ritorna ciò che dicono dell'integrale vicino a ogni estremo, in result[]
 * (due per parte, come per il confronto), o 0 se un limite non si calcola. */
static int improper_limits(const char *function, int x, EndText *from, EndText *to, ImproperResult *result) {
    char where[ANSWER_BYTES], intro[2 * ANSWER_BYTES];
    for (int i = 0; i < improper_pieces; i++) {
        for (int end = 0; end < 2; end++) {
            const EndText *point = &improper_point[i + end];
            EndText *limit = end ? &to[i] : &from[i];
            end_latex(point, where, sizeof where);
            snprintf(intro, sizeof intro, "\n\\emph{The limit of $F$ as $%c \\to %s%s$}.\n", x, where, point->infinite ? "" : end ? "^{-}" : "^{+}");
            if (!improper_limit(function, x, point, end ? -1 : 1, intro, limit)) return 0;

            /* Vicino all'estremo destro l'integrale va come F, vicino al
             * sinistro come -F. */
            int sign = end ? limit->infinite : -limit->infinite;
            result[2 * i + end] = sign > 0 ? IMPROPER_PLUS : sign < 0 ? IMPROPER_MINUS : IMPROPER_FINITE;
        }
    }
    return 1;
}

/* 30k-4. Il controllo con i numeri sulla parte da p a q, con f e F già
 * passati da sample_tree(): vedi la testa di 30k. Mette in *steps quanti
 * intervalli [p_k, q_k] sono stati controllati, e dell'ultimo gli estremi in
 * *low e *high e l'involucro dell'integrale in *integral. Ritorna 1 se il controllo non trova errori; 0 se dice che il
 * programma ha sbagliato, F(q_k) - F(p_k) di sicuro fuori dall'involucro o
 * due stime garantite che non si toccano; -1 se trova un intervallo
 * compatto della parte su cui f non si chiude benché si calcoli nei suoi
 * estremi. */
static int improper_riemann(const Node *f, const Node *F, int x, const EndText *p, const EndText *q, int *steps, Range *low, Range *high,
                            Range *integral) {
    Range P = range_none(), Q = range_none(), one = range_ratio(1, 1), sum = {0, 0};
    *steps = 0;
    if ((!p->infinite && !end_range(p, x, &P)) || (!q->infinite && !end_range(q, x, &Q))) return 1;

    /* Il punto di partenza m, dentro la parte; poi gli intervalli verso gli
     * estremi, a metà della distanza che resta o raddoppiando. */
    Range m = p->infinite && q->infinite ? (Range){0, 0} : p->infinite ? range_sub(Q, one) : q->infinite ? range_add(P, one)
                                                                                                      : range_div(range_add(P, Q), range_ratio(2, 1));
    Range left = m, right = m;
    for (int k = 1; k <= IMPROPER_STEPS; k++) {
        Range half = range_ratio(1, (__int128)1 << k), far = range_ratio((__int128)1 << (k - 1), 1);
        Range next_left = p->infinite ? range_sub(m, far) : range_add(P, range_mul(range_sub(m, P), half));
        Range next_right = q->infinite ? range_add(m, far) : range_sub(Q, range_mul(range_sub(Q, m), half));
        /* Una sola suddivisione, senza raffinarla: qui l'involucro serve a
         * vedere un F sbagliato, non a dare il valore con tante cifre, e
         * le parti sono tante (due per passo e per parte). */
        Enclosure before = riemann_enclosure(f, F, x, next_left, left, RIEMANN_PIECES), after = riemann_enclosure(f, F, x, right, next_right, RIEMANN_PIECES);
        if (before.broken || after.broken) return 0;

        /* Un intervallo che gli intervalli non sanno chiudere ferma il
         * controllo. Può essere F a non chiudersi, per i conti (2/(3x^3 -
         * 45x^2 + 225x - 375) vicino a 5 perde tutte le cifre); ma se è f a
         * non chiudersi, e f si calcola in tutti e due i suoi estremi, il
         * motivo non è un numero troppo grande vicino a un estremo
         * dell'integrale, ma forse un punto dentro in cui f non è definita,
         * che le condizioni di esistenza (30k-1) non hanno visto: allora il
         * controllo smentisce. */
        for (int side = 0; side < 2; side++) {
            Range from = side ? right : next_left, to = side ? next_right : left;
            if ((side ? after : before).defined || !range_known(sample_value(f, x, from)) || !range_known(sample_value(f, x, to))) continue;
            if (!riemann_enclosure(f, NULL, x, from, to, RIEMANN_PIECES).defined) return -1;
        }
        if (!before.defined || !after.defined) break;
        sum = range_add(sum, range_add(before.integral, after.integral));
        Range difference = range_sub(sample_value(F, x, next_right), sample_value(F, x, next_left));
        if (!range_known(sum) || !range_known(difference)) break;
        if (difference.high < sum.low || difference.low > sum.high) return 0;
        left = next_left;
        right = next_right;
        *steps = k;
        *low = left;
        *high = right;
        *integral = sum;
    }
    return 1;
}

/* Il motivo di un NON DIMOSTRATO quando il confronto dice che l'integrale
 * converge, ma il valore manca. */
static const char *const CONVERGES_WITHOUT_VALUE = "l'integrale converge (per confronto), ma non trovo una primitiva per calcolarne il valore";

/* 30k. Il verdetto su un integrale improprio, letto da formula: vedi la
 * testa di 30k e di 30l. Svuota l'arena e la tabella degli atomi. */
static Verdict prove_improper(const char *formula) {
    static char f_text[ANSWER_BYTES], F_text[ANSWER_BYTES], f_conditions[ANSWER_BYTES], all_conditions[2 * ANSWER_BYTES], answer[ANSWER_BYTES];
    static EndText from[MAX_IMPROPER_PIECES], to[MAX_IMPROPER_PIECES];
    static ImproperResult ends[2 * MAX_IMPROPER_PIECES];
    Verdict verdict = {NOT_PROVED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    IntegralStatement st;
    PrimitiveCheck check;

    /* La lettura, i testi, e il verso: gli estremi da sinistra a destra. */
    proof_reset();
    integral_reset();
    if (!parse_integral_statement(formula, &st)) {
        verdict.outcome = UNSUPPORTED;
        verdict.reason = syntax_error;
        syntax_error = NULL;
        return verdict;
    }
    int x = st.variable, flip = 0;
    if (x == 'n') {
        verdict.outcome = UNSUPPORTED;
        verdict.reason = "un integrale improprio nella lettera n, che nei limiti è l'indice di una successione";
        return verdict;
    }
    EndText a = {st.lower_infinite, ""}, b = {st.upper_infinite, ""};
    if ((st.lower && !node_latex(st.lower, a.text, sizeof a.text)) || (st.upper && !node_latex(st.upper, b.text, sizeof b.text)) ||
        !node_latex(st.integrand, f_text, sizeof f_text)) {
        verdict.reason = "un estremo, o la funzione integranda, troppo lunghi da scrivere";
        return verdict;
    }
    if (a.infinite || b.infinite) {
        if (a.infinite == b.infinite) { verdict.reason = "i due estremi sono lo stesso infinito"; return verdict; }
        flip = a.infinite > 0 || b.infinite < 0;
    } else {
        Range low, high;
        int side;
        if (!end_range(&a, x, &low) || !end_range(&b, x, &high) || !range_side(range_sub(high, low), &side)) {
            verdict.reason = "non riesco a stabilire quale dei due estremi è il più piccolo";
            return verdict;
        }
        flip = side < 0;
    }
    improper_pieces = 1;
    improper_point[0] = flip ? b : a;
    improper_point[1] = flip ? a : b;

    /* Le condizioni di esistenza di f; la primitiva, e le sue. */
    f_conditions[0] = all_conditions[0] = 0;
    if (!domain_conditions(st.integrand, x, f_conditions, sizeof f_conditions)) {
        verdict.reason = "la funzione integranda contiene ciò di cui non so scrivere le condizioni di esistenza";
        return verdict;
    }
    Node *F = found_primitive(st.integrand, x, F_text, sizeof F_text, &check);
    failure = NULL;
    proof_add("\\textbf{Proof.} The integral is improper: by definition it is the limit of the integrals over the compact intervals inside "
              "the interval of integration, with the interval split at the points where the functions are not defined; it converges if "
              "the limit is finite on every part. ");
    size_t opening = proof_length;
    int with_F = 0;
    if (F) {
        snprintf(all_conditions, sizeof all_conditions, "%s", f_conditions);
        with_F = domain_conditions(F, x, all_conditions, sizeof all_conditions) && check.derivative &&
                 domain_conditions(check.derivative, x, all_conditions, sizeof all_conditions);
        if (with_F) {
            proof_add("Let $F = ");
            put_node(F, 0);
            proof_add("$, found by the search for an antiderivative. ");
            if (!put_primitive_check(st.integrand, F, x, &check)) {
                unjustified_steps++;
                verdict.reason = "la derivata scritta nella dimostrazione, riletta, non è confermata";
                return verdict;
            }
            proof_add("By the fundamental theorem of calculus, on every compact interval $[p, q]$ where $f$ is continuous and $F$ "
                      "differentiable, the integral is $F(q) - F(p)$: on each part, the improper integral is the limit of $F$ at its right end "
                      "minus the limit at its left end.\n\n");
        }
    }

    /* 30k-1, 30k-3: dove le funzioni sono definite, poi i limiti di F.
     * Se non si arriva in fondo, si ricomincia con il confronto (30l), senza
     * F e senza ciò che se n'è scritto. */
    ImproperResult result = IMPROPER_UNKNOWN;
    if (with_F && improper_domain(all_conditions, x) && improper_limits(F_text, x, from, to, ends)) result = improper_combine(ends, 2 * improper_pieces);
    if (result == IMPROPER_UNKNOWN) {
        proof_cut(opening);
        with_F = 0;
        improper_pieces = 1;
        improper_point[0] = flip ? b : a;
        improper_point[1] = flip ? a : b;
        if (!improper_domain(f_conditions, x)) {
            verdict.reason = "non riesco a stabilire che la funzione integranda sia continua sull'intervallo aperto di integrazione";
            return verdict;
        }
        for (int i = 0; i < 2 * improper_pieces; i++) ends[i] = improper_compare(f_text, x, &improper_point[(i + 1) / 2], i % 2 ? -1 : 1, 1);
        result = improper_combine(ends, 2 * improper_pieces);
    } else {
        /* Il secondo controllo della convergenza: il confronto, che non usa
         * F, dove sa decidere, deve dire lo stesso (30k-4). Del suo
         * ragionamento nel testo resta solo l'esito. */
        ImproperResult again[2 * MAX_IMPROPER_PIECES];
        size_t mark = proof_length;
        for (int i = 0; i < 2 * improper_pieces; i++) again[i] = improper_compare(f_text, x, &improper_point[(i + 1) / 2], i % 2 ? -1 : 1, 0);
        proof_cut(mark);
        for (int i = 0; i < 2 * improper_pieces; i++) {
            if (again[i] == IMPROPER_UNKNOWN || again[i] == ends[i]) continue;
            unjustified_steps++;
            verdict.reason = "il confronto e i limiti della primitiva non sono d'accordo sulla convergenza: un errore del programma";
            return verdict;
        }
        int compared = 0;
        for (int i = 0; i < 2 * improper_pieces; i++) compared += again[i] != IMPROPER_UNKNOWN;
        if (compared)
            proof_add("\n\\emph{Second check, by comparison} (which does not use $F$): at %d of the %d ends the behaviour of the integrand, "
                      "compared with a power of the distance from the end and of its logarithm, gives the same convergence or divergence.\n",
                      compared, 2 * improper_pieces);
    }
    if (flip) result = result == IMPROPER_PLUS ? IMPROPER_MINUS : result == IMPROPER_MINUS ? IMPROPER_PLUS : result;

    /* Da qui servono di nuovo gli alberi: si rileggono dai testi. */
    integral_reset();
    parse_integral_statement(formula, &st);
    syntax_error = NULL;

    /* 30k-4. Il controllo con i numeri, su ogni parte, con F. */
    if (with_F) {
        Node *fs = sample_tree(text_tree(f_text), x, 0, 0), *Fs = sample_tree(text_tree(F_text), x, 0, 0);
        proof_add("\n\\emph{Check with numbers}, with Riemann sums in interval arithmetic, which use neither $F$ nor exact algebra: ");
        for (int i = 0; i < improper_pieces; i++) {
            int steps;
            Range low, high, integral;
            int checked = improper_riemann(fs, Fs, x, &improper_point[i], &improper_point[i + 1], &steps, &low, &high, &integral);
            if (checked <= 0) {
                unjustified_steps++;
                verdict.reason = checked ? "su un intervallo compatto dentro una parte gli intervalli non sanno chiudere la funzione integranda, benché "
                                           "la calcolino nei suoi estremi: forse un punto in cui non è definita, che le condizioni di esistenza non hanno visto"
                                         : "F(q) - F(p) non sta nell'involucro di Riemann dell'integrale su [p, q]: un errore del programma";
                return verdict;
            }
            if (!steps) { verdict.reason = "le somme di Riemann con gli intervalli non si calcolano vicino agli estremi"; return verdict; }
            if (improper_pieces > 1) proof_add("%son part %d, ", i ? "; " : "", i + 1);
            proof_add("on %d intervals $[p_k, q_k]$ growing towards the ends they enclose the integral, and $F(q_k) - F(p_k)$ lies inside every "
                      "time; the last is $[p_k, q_k] \\subseteq ", steps);
            put_range((Range){low.low, high.high});
            proof_add("$, with the integral in $");
            put_range(integral);
            proof_add("$");
        }
        proof_add(".\n\n");
    }

    /* Il valore, per una parte alla volta, con i conti esatti. */
    Rat exact = rat_int(0);
    if (with_F && result == IMPROPER_FINITE) {
        for (int i = 0; i < improper_pieces && !failure; i++) {
            Node *above = text_tree(to[i].text), *below = text_tree(from[i].text);
            env_count = 0;
            if (!above || !below) { verdict.reason = "un limite scritto non si rilegge"; return verdict; }
            exact = rat_add(exact, rat_add(eval(above), eval(below), 1), 0);
        }
        if (flip) exact = rat_add(rat_int(0), exact, 1);
        if (failure) { verdict.reason = failure; failure = NULL; return verdict; }
    }

    /* Il verdetto: holds è 1 se l'enunciato è vero, 0 se è falso, -1 se non
     * si sa. */
    int holds = -1;
    const char *method = with_F ? "come integrale improprio, con la primitiva e i suoi limiti agli estremi" : "come integrale improprio, per confronto";
    int divergent = result == IMPROPER_PLUS || result == IMPROPER_MINUS || result == IMPROPER_NEITHER || result == IMPROPER_DIVERGENT;
    if (st.membership) holds = result == IMPROPER_FINITE ? st.membership > 0 : divergent ? st.membership < 0 : -1;
    else if (st.answer_infinite) holds = result == IMPROPER_PLUS ? st.answer_infinite > 0 : result == IMPROPER_MINUS ? st.answer_infinite < 0
                                        : result == IMPROPER_FINITE || result == IMPROPER_NEITHER ? 0 : -1;
    else if (st.answer && divergent) holds = 0;
    else if (st.answer && result == IMPROPER_FINITE && with_F) {
        env_count = 0;
        Rat gap = rat_add(exact, eval(st.answer), 1);
        int side;
        if (!failure && poly_vanishes(gap.num)) holds = 1;
        else if (!failure && range_side(constant_range(gap), &side)) holds = 0;
        failure = NULL;
    }

    /* La conclusione scritta. */
    if (result == IMPROPER_FINITE) proof_add("Hence the integral converges");
    else if (result == IMPROPER_PLUS || result == IMPROPER_MINUS) proof_add("Hence the integral is $%s\\infty$", result == IMPROPER_PLUS ? "+" : "-");
    else if (result == IMPROPER_NEITHER) proof_add("Hence the integral does not converge: on one part it is $+\\infty$ and on another $-\\infty$, and the sum has no value");
    else if (result == IMPROPER_DIVERGENT) proof_add("Hence the integral does not converge, because it diverges near one end");
    if (!st.answer && !st.answer_infinite && !st.membership) {
        /* Una richiesta: il valore, o l'infinito, scritto e riletto. */
        verdict.method = method;
        if (result == IMPROPER_PLUS || result == IMPROPER_MINUS) snprintf(answer, sizeof answer, "%s\\infty", result == IMPROPER_PLUS ? "+" : "-");
        else if (result == IMPROPER_FINITE && with_F) {
            Node *back = rat_latex(exact, answer, sizeof answer) ? text_tree(answer) : NULL;
            env_count = 0;
            Rat gap = back ? rat_add(exact, eval(back), 1) : rat_int(1);
            if (!back || failure || !poly_vanishes(gap.num)) {
                failure = NULL;
                unjustified_steps += back != NULL;
                verdict.reason = back ? "il valore scritto, riletto, non è quello calcolato" : "non riesco a scrivere il valore dell'integrale";
                return verdict;
            }
            proof_add(", and its value is $%s$", answer);
        } else {
            verdict.reason = result == IMPROPER_FINITE ? CONVERGES_WITHOUT_VALUE
                           : result == IMPROPER_NEITHER ? "l'integrale non converge, e non vale né +\\infty né -\\infty"
                           : result == IMPROPER_DIVERGENT ? "l'integrale non converge, ma non so se valga un infinito"
                           : "non so stabilire se l'integrale converge";
            return verdict;
        }
        proof_add(". $\\Box$");
        verdict.outcome = SOLVED;
        verdict.detail = answer;
        verdict.reason = "gli integrali non hanno una notazione nei certificati";
        verdict.proof = proof_text;
        return verdict;
    }
    if (holds < 0) {
        verdict.reason = result == IMPROPER_UNKNOWN ? "non so stabilire se l'integrale converge"
                       : result == IMPROPER_FINITE && !with_F ? CONVERGES_WITHOUT_VALUE
                       : result == IMPROPER_DIVERGENT ? "l'integrale non converge, ma non so se valga un infinito"
                       : "non so se il valore calcolato è quello scritto";
        return verdict;
    }
    if (result == IMPROPER_FINITE && with_F && rat_latex(exact, answer, sizeof answer)) proof_add(", and its value is $%s$", answer);
    proof_add(holds ? ". This is what the statement says. $\\Box$" : ". The statement says otherwise, so it is false. $\\Box$");
    verdict.outcome = holds ? PROVED : REFUTED;
    verdict.method = method;
    verdict.reason = "gli integrali non hanno una notazione nei certificati";
    verdict.proof = proof_text;
    return verdict;
}

/* Prova a dimostrare, o a risolvere, l'enunciato su un integrale scritto in
 * formula (vedi 9j e la testa del capitolo). Svuota l'arena e la tabella
 * degli atomi: i risultati di chiamate precedenti non sono più validi. */
static Verdict prove_integral(const char *formula) {
    static char answer[ANSWER_BYTES + 8];
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    IntegralStatement statement;

    /* Ripartenza da zero; nessuna variabile di induzione. */
    proof_reset();
    integral_reset();
    if (!parse_integral_statement(formula, &statement)) {
        verdict.reason = syntax_error;
        syntax_error = NULL;
        return verdict;
    }
    int x = statement.variable;
    const Node *f = statement.integrand, *claim = statement.answer;
    if (x == 'e' || !only_letters(f, x) || !only_letters(claim, x) || !only_letters(statement.lower, 0) || !only_letters(statement.upper, 0)) {
        verdict.reason = "in un integrale le sole lettere ammesse sono la variabile, e e pi greco";
        return verdict;
    }

    /* Un integrale definito: improprio (30k) se ha un estremo infinito, se
     * dice di valere un infinito o di convergere, o se 30i non riesce a
     * vedere la funzione continua su tutto [a, b]. */
    if (statement.definite) {
        int improper = statement.lower_infinite || statement.upper_infinite || statement.answer_infinite || statement.membership;
        if (!improper) verdict = prove_definite(f, statement.lower, statement.upper, claim, x, &improper);
        return improper ? prove_improper(formula) : verdict;
    }

    /* Una primitiva da verificare. */
    if (claim) {
        PrimitiveCheck check = primitive_check(f, claim, x);
        verdict = primitive_verdict(&check, x);
        if (check.outcome != PROVED) return verdict;
        proof_add("\\textbf{Proof.} ");
        if (!put_primitive_check(f, claim, x, &check)) {
            unjustified_steps++;
            verdict.outcome = NOT_PROVED;
            verdict.reason = "la derivata scritta nella dimostrazione, riletta, non è confermata";
            return verdict;
        }
        proof_add("$\\Box$");
        verdict.method = check.outside ? "con le regole di derivazione, su ogni intervallo in cui primitiva e funzione integranda sono definite "
                                         "(la primitiva non lo è dappertutto dove lo è la funzione)"
                                       : "con le regole di derivazione, su ogni intervallo in cui primitiva e funzione integranda sono definite";
        verdict.reason = NULL;
        verdict.proof = proof_text;
        calculus_certify(&verdict, calculus_certificate("antiderivative", x, NULL, claim, f, NULL, NULL, NULL), claim, x);
        return verdict;
    }

    /* Una primitiva da trovare. */
    PrimitiveCheck check;
    char primitive[ANSWER_BYTES];
    Node *F = found_primitive(f, x, primitive, sizeof primitive, &check);
    verdict.outcome = NOT_PROVED;
    verdict.reason = check.reason;
    if (!F) return verdict;
    proof_add("\\textbf{Solution.} The search for an antiderivative gives $");
    put_node(F, 0);
    proof_add("$, which is checked as any stated antiderivative. ");
    if (!put_primitive_check(f, F, x, &check)) {
        unjustified_steps++;
        verdict.reason = "la derivata scritta nella dimostrazione, riletta, non è confermata";
        return verdict;
    }
    proof_add("$\\Box$");
    snprintf(answer, sizeof answer, "%s + c", primitive);
    verdict.outcome = SOLVED;
    verdict.reason = NULL;
    verdict.method = primitive_method ? primitive_method : "";
    verdict.detail = answer;
    verdict.note = check.outside ? "c costante su ogni intervallo; la primitiva non è definita dappertutto dove lo è la funzione" : "c costante su ogni intervallo";
    verdict.proof = proof_text;
    calculus_certify(&verdict, calculus_certificate("antiderivative", x, NULL, F, f, NULL, NULL, NULL), F, x);
    return verdict;
}

