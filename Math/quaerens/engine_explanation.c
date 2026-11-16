/* MODULO engine_explanation: la spiegazione: i passaggi registrati e
 * ricontrollati (capitolo 40).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_explanation.h,
 * e il resto è static. */
#include "engine_explanation.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"
#include "engine_intervals.h"
#include "engine_quantifiers.h"
#include "engine_sign_tables.h"

/* =============================================================================
 * 40. LA SPIEGAZIONE: I PASSAGGI REGISTRATI E RICONTROLLATI
 * ============================================================================
 *
 * A che cosa serve. Una dimostrazione dice perché un enunciato è vero; chi
 * studia vuole anche vedere come ci si arriva, un passaggio alla volta, come
 * alla lavagna: "porto tutto a primo membro, metto a denominatore comune,
 * raccolgo i fattori, guardo dove si annullano, faccio la tabella dei segni,
 * provo un valore in ogni intervallo". Di \frac{x - 2}{x + 3} \ge x la
 * dimostrazione scritta dal capitolo 18.16 elenca le righe della tabella;
 * qui si registra la strada:
 *
 *     \frac{x - 2}{x + 3} - x \ge 0          (tutto a un membro)
 *     \frac{-x^{2} - 2x - 2}{x + 3} \ge 0    (una sola frazione)
 *     \frac{-(x^{2} + 2x + 2)}{x + 3} \ge 0  (i fattori)
 *
 * poi gli zeri di ogni fattore, la tabella con una riga per fattore, e i
 * valori dei due membri in un punto di ogni intervallo.
 *
 * IL PRINCIPIO
 *
 * Si spiega ciò che il motore ha fatto davvero, e ogni passaggio mostrato è
 * un fatto ricontrollato. Un passaggio falso in una spiegazione è grave
 * quanto una dimostrazione falsa: chi legge lo impara.
 *
 *   - La spiegazione è un dato (Explanation): passi con il loro tipo e le
 *     loro formule, e una tabella di segni. Non contiene frasi: quelle le
 *     scrive output.c (capitolo 41), una per tipo di passo, senza calcolare
 *     e senza decidere nulla.
 *   - Niente strade inventate. La differenza dei due membri è quella che
 *     calcola la valutazione (capitolo 11), come in sign_fraction(); i
 *     fattori sono quelli della tabella (la base di 18p-4 e le radici
 *     razionali), i punti e i segni sono quelli delle sue righe. Non c'è una
 *     formula risolutiva per un tipo di esercizio: se il motore non ha
 *     usato una strada, qui non compare.
 *   - Ogni anello è ricontrollato per una strada diversa da quella che lo
 *     ha prodotto (40a), e sempre a partire dal testo che verrà stampato.
 *     Un anello che non regge non si mostra: con lui cade tutta la
 *     spiegazione dell'enunciato, perché una catena con un buco non spiega,
 *     e unjustified_steps sale. Il verdetto non cambia: questo capitolo
 *     viene dopo, e non decide.
 *
 * 40a. I CONTROLLI
 *
 * Chi scrive parte dagli alberi dell'enunciato e dai polinomi a coefficienti
 * interi della tabella (Uni, 18.8). Chi controlla parte dai caratteri: il
 * testo scritto viene riletto con il lettore degli enunciati, come se lo
 * avesse scritto l'utente, e calcolato con le frazioni di polinomi negli
 * atomi (capitoli 5-7 e 11). Un segno sbagliato, una parentesi mancante, un
 * fattore dimenticato cambiano il valore di ciò che si rilegge.
 *
 *   - Due forme consecutive della catena (explain_equals()): il testo
 *     riletto meno la differenza dei due membri dell'enunciato deve essere
 *     zero per il test di annullamento del capitolo 12.
 *   - Uno zero di un fattore, e ogni cella della tabella
 *     (explain_sign_at()): il valore della colonna si sostituisce nel testo
 *     riletto, con il conto esatto. Un punto irrazionale è la radice di un
 *     polinomio di secondo grado: si sostituisce la sua scrittura con i
 *     radicali, e il test di annullamento per le radici di interi è esatto.
 *     Il segno trovato deve essere quello che la tabella del motore ha
 *     usato, e il prodotto dei segni dei fattori quello della frazione.
 *   - La verità di ogni confronto e della condizione in ogni colonna
 *     (explain_holds()): ricalcolata allo stesso modo, deve essere quella
 *     di sign_truth().
 *   - Che un fattore non si annulli mai: per uno di secondo grado il
 *     discriminante negativo, un conto a sé; per uno di grado più alto
 *     serve che checker.c abbia accettato il certificato della tabella,
 *     perché è lui che riconta le radici con Sturm (18p-15).
 *   - I valori di prova: i due membri calcolati con il conto esatto devono
 *     stare negli intervalli che il capitolo 24 dà per gli stessi membri.
 *   - Ogni altro testo che si stampa: un numero (un punto, un valore di
 *     prova) si rilegge e deve essere quello con cui si è fatto il conto
 *     (explain_number_is()); una condizione (un confronto com'è scritto,
 *     l'intestazione di una colonna) si rilegge e deve valere nelle colonne
 *     giuste (explain_condition(), explain_columns()).
 *
 * CHE COSA SI SPIEGA, E CHE COSA NON ANCORA
 *
 * Gli enunciati decisi direttamente dalla tabella dei segni (18p) in una
 * variabile, i cui confronti sono tra espressioni razionali: interi, la
 * variabile, le quattro operazioni, potenze con esponente intero. Sono le
 * equazioni e le disequazioni intere e fratte, i loro sistemi, e gli
 * enunciati che ne affermano il risultato. Restano fuori, e il documento
 * riporta allora la sola dimostrazione di sempre:
 *
 *   - i valori assoluti: servirebbe un passo "per casi" per ogni scelta dei
 *     segni degli argomenti, che la tabella ha già (SignAtom.by_pattern);
 *   - le radici quadrate, gli esponenziali, i logaritmi e le funzioni
 *     goniometriche: un passo per la regola di 18p-7 e uno per la
 *     sostituzione con la lettera (18p-8, 18p-11);
 *   - i punti che sono radici senza una scrittura con i radicali (grado da
 *     tre in su): lì il valore della colonna non si può sostituire, e i
 *     controlli di 40a non si possono fare;
 *   - un enunciato con una negazione davanti, quelli con un parametro
 *     (18t), gli studi di funzione (27j), e le tabelle con più di
 *     MAX_EXPLAIN_COLUMNS colonne.
 *
 * Il contenitore serve a ogni famiglia di enunciati: ognuna ha i suoi tipi
 * di passo, registrati dove sta il suo metodo, e in output.c le sue frasi.
 * Le derivate richieste si spiegano una regola alla volta, nel capitolo 27
 * (27n), e lì ogni riga la ricontrolla checker.c. Le uguaglianze
 * dimostrate per induzione si spiegano in fondo a questo capitolo (40b):
 * i primi valori dei due membri, in tabella e in un grafico, e il passo
 * svolto come un conto. Limiti e integrali non hanno ancora i loro passi.
 *
 * PERCHÉ QUI
 *
 * Il capitolo legge lo stato che la tabella dei segni lascia dietro di sé
 * (i confronti preparati, la base, i punti, le righe), e lo chiama chi ha
 * appena avuto il verdetto e il certificato, nel capitolo 19: sta quindi tra
 * i due. Il numero 40 dice solo che è nato dopo.
 */

/* Il contenuto di una casella: per una riga di segni -1, 0, 1 oppure
 * EXPLAIN_NO_VALUE; per una riga di verità 1 (vero) o 0 (falso). */
enum { EXPLAIN_NO_VALUE = 2 };

/* La spiegazione dell'ultimo enunciato, se ne ha una. Come il grafico
 * (18q), appartiene al motore, che la svuota quando comincia l'enunciato
 * successivo (prove_core()); chi scrive il documento la legge prima.
 * explanations_wanted dice se le spiegazioni servono: finché nessuno le
 * mette in un documento non vengono costruite. */
_Thread_local Explanation explanation;
_Thread_local int explanations_wanted;

/* Lo stato della spiegazione in corso. explain_wrong: un anello non ha
 * superato un controllo di 40a, o ciò che si è scritto non si rilegge.
 * explain_broken: un limite del programma (numeri troppo grandi, troppo
 * testo, troppe colonne) ha impedito di scrivere o di controllare. In tutti
 * e due i casi la spiegazione si abbandona; solo il primo è un errore. */
_Thread_local int explain_wrong, explain_broken;

/* Il testo della dimostrazione messo da parte mentre si scrive una
 * spiegazione (explain_capture()). */
static _Thread_local struct {
    char *text;
    size_t length, capacity;
    int growable, broken;
} explain_proof;

/* Con on = 1 devia nel deposito della spiegazione tutto ciò che scrive
 * proof_add(); con on = 0 rimette al suo posto il testo della dimostrazione.
 *
 * Perché deviare invece di riscrivere. Le formule di una spiegazione si
 * scrivono con le stesse funzioni delle dimostrazioni (put_node(),
 * put_uni(), put_wide()), che scrivono dove scrive proof_add(): ciò che
 * scrivono si rilegge, ed è già messo alla prova da tutti i test. Una
 * seconda famiglia di funzioni uguali, con un altro deposito, sarebbe solo
 * un secondo posto in cui sbagliare una parentesi. La dimostrazione già
 * scritta, a cui punta il verdetto, non viene toccata. */
void explain_capture(int on) {
    if (on) {
        explain_proof.text = proof_text;
        explain_proof.length = proof_length;
        explain_proof.capacity = proof_capacity;
        explain_proof.growable = proof_growable;
        explain_proof.broken = proof_broken;
        proof_text = explanation.text;
        proof_capacity = sizeof explanation.text;
        proof_length = 0;
        proof_growable = proof_broken = 0;
        proof_text[0] = 0;
        return;
    }
    proof_text = explain_proof.text;
    proof_length = explain_proof.length;
    proof_capacity = explain_proof.capacity;
    proof_growable = explain_proof.growable;
    proof_broken = explain_proof.broken;
}

/* Chiude il pezzo di testo cominciato in start (il valore che proof_length
 * aveva prima di scriverlo) e lo ritorna: una stringa a sé dentro il
 * deposito. Se il deposito è finito annota il limite e ritorna un testo
 * vuoto. */
const char *explain_piece(size_t start) {
    if (proof_broken || proof_length + 1 >= proof_capacity) { explain_broken = 1; return ""; }

    /* Lo zero che chiude il pezzo resta nel deposito: il prossimo comincia
     * dopo. */
    proof_text[proof_length++] = 0;
    proof_text[proof_length] = 0;
    return proof_text + start;
}

/* Aggiunge un passo del tipo kind, per il confronto group, e lo ritorna con
 * gli altri campi a zero. Se i passi sono troppi annota il limite e ritorna
 * un passo di riserva. */
ExplainStep *explain_step(ExplainKind kind, int group) {
    static _Thread_local ExplainStep spare;
    ExplainStep *step = &spare;
    if (explanation.steps == MAX_EXPLAIN_STEPS) explain_broken = 1;
    else step = &explanation.step[explanation.steps++];
    memset(step, 0, sizeof *step);
    step->kind = kind;
    step->group = group;
    return step;
}

/* Aggiunge alla tabella una riga del tipo kind, per il confronto group, con
 * la formula label, e la ritorna. Se le righe sono troppe annota il limite
 * e ritorna una riga di riserva. */
static ExplainLine *explain_line(ExplainLineKind kind, int group, const char *label) {
    static _Thread_local ExplainLine spare;
    ExplainLine *line = &spare;
    if (explanation.lines == MAX_EXPLAIN_LINES) explain_broken = 1;
    else line = &explanation.line[explanation.lines++];
    memset(line, 0, sizeof *line);
    line->kind = kind;
    line->group = group;
    line->label = label;
    return line;
}

/* 40a. Ritorna 1 se l'espressione scritta in text, riletta con il lettore
 * degli enunciati, è uguale a expected per il test di annullamento del
 * capitolo 12, dove tutte e due hanno un valore. Altrimenti ritorna 0 e
 * annota perché: explain_wrong se il testo non si rilegge o dice un'altra
 * cosa, explain_broken se il conto non riesce. */
static int explain_equals(const char *text, Rat expected) {
    Node *written = parse_expression(text);
    if (syntax_error) { syntax_error = NULL; explain_wrong = 1; return 0; }
    env_count = 0;
    Rat gap = rat_add(eval(written), expected, 1);
    int same = !failure && (gap.num.count == 0 || poly_vanishes(gap.num));
    if (failure) { failure = NULL; explain_broken = 1; return 0; }
    if (!same) explain_wrong = 1;
    return same;
}

/* 40a. Calcola l'espressione node quando la variabile name vale value, con
 * il conto esatto: mette in *side il segno del risultato, e in *defined 1
 * se lì l'espressione ha un valore, 0 se non lo ha (una divisione per zero).
 * value è un razionale, oppure un numero con radici quadrate di interi.
 * Ritorna 0, e annota il limite, se il conto non riesce a dirlo. */
static int explain_sign_at(const Node *node, int name, Rat value, int *side, int *defined) {
    *side = 0;
    *defined = 1;
    undefined = 0;
    env_count = 0;
    env_push(name, value);
    Rat result = eval(node);
    env_count = 0;
    if (failure && undefined) { failure = NULL; undefined = 0; *defined = 0; return 1; }
    if (failure || !number_sign(result, side)) { failure = NULL; explain_broken = 1; return 0; }
    return 1;
}

/* Ritorna 1 se il confronto f vale quando la differenza tra il membro
 * scritto a sinistra e quello scritto a destra ha il segno side. Il lettore
 * scambia i membri di > e \ge (Formula.swapped): qui si torna a come erano
 * scritti. */
static int explain_relation_holds(const Formula *f, int side) {
    switch (f->kind) {
    case F_EQUAL:    return side == 0;
    case F_DISTINCT: return side != 0;
    case F_LESS:     return f->swapped ? side > 0 : side < 0;
    default:         return f->swapped ? side >= 0 : side <= 0;
    }
}

/* Ritorna il segno di confronto di f in LaTeX, com'era scritto. */
static const char *explain_relation(const Formula *f) {
    switch (f->kind) {
    case F_EQUAL:    return "=";
    case F_DISTINCT: return "\\neq";
    case F_LESS:     return f->swapped ? ">" : "<";
    default:         return f->swapped ? "\\ge" : "\\le";
    }
}

/* 40a. Ritorna 1 se la condizione f, senza quantificatori, vale quando la
 * variabile name vale value, calcolando ogni confronto con il conto esatto
 * (explain_sign_at()); un confronto in cui un membro non ha un valore non
 * vale. È sign_holds_at() (18.12) per un valore che può avere radici. Se un
 * conto non riesce il limite resta annotato in explain_broken, e la
 * risposta non vuol dire nulla. */
static int explain_holds(const Formula *f, int name, Rat value) {
    switch (f->kind) {
    case F_AND:     return explain_holds(f->a, name, value) && explain_holds(f->b, name, value);
    case F_OR:      return explain_holds(f->a, name, value) || explain_holds(f->b, name, value);
    case F_IMPLIES: return !explain_holds(f->a, name, value) || explain_holds(f->b, name, value);
    case F_IFF:     return explain_holds(f->a, name, value) == explain_holds(f->b, name, value);
    case F_NOT:     return !explain_holds(f->a, name, value);
    default:        break;
    }
    int side = 0, defined = 1;
    if (!explain_sign_at(node_new(N_SUB, f->left, f->right), name, value, &side, &defined) || !defined) return 0;
    return f->kind == F_EQUAL ? side == 0 : f->kind == F_DISTINCT ? side != 0 : f->kind == F_LESS ? side < 0 : side <= 0;
}

/* Scrive la condizione f, senza quantificatori, com'era scritta: ogni
 * confronto con i suoi due membri al loro posto e il suo segno, e i
 * connettivi tra un confronto e l'altro. Una parte che è a sua volta un
 * connettivo va tra parentesi se è di un tipo diverso da quello che la
 * contiene: così ciò che si scrive si rilegge allo stesso modo qualunque
 * sia la precedenza dei connettivi.
 *
 * Perché non il testo dell'enunciato (put_source()). Il pezzo di testo di
 * una condizione scritta con \begin{cases} finisce prima di \end{cases}, e
 * da solo non è LaTeX; e ciò che si scrive qui viene riletto e confrontato
 * con la tabella (explain_condition()), cosa che per il testo di partenza
 * non direbbe nulla. */
static void put_written(const Formula *f) {
    static const char *const joint[] = {[F_AND] = "\\land", [F_OR] = "\\lor", [F_IMPLIES] = "\\implies", [F_IFF] = "\\iff"};
    if (f->kind < F_AND) {
        put_node(f->swapped ? f->right : f->left, 0);
        proof_add(" %s ", explain_relation(f));
        put_node(f->swapped ? f->left : f->right, 0);
        return;
    }
    if (f->kind == F_NOT) proof_add("\\lnot ");
    for (int side = 0; side < (f->kind == F_NOT ? 1 : 2); side++) {
        const Formula *part = side ? f->b : f->a;
        int wrap = part->kind >= F_AND && (part->kind != f->kind || f->kind == F_IMPLIES || f->kind == F_NOT);
        if (side) proof_add(" %s ", joint[f->kind]);
        if (wrap) proof_add("\\left(");
        put_written(part);
        if (wrap) proof_add("\\right)");
    }
}

/* Ritorna 1 se nell'espressione node compare una funzione: un valore
 * assoluto, una radice, un logaritmo. */
static int node_has_call(const Node *node) {
    if (!node) return 0;
    return node->kind == N_CALL || node_has_call(node->a) || node_has_call(node->b) || node_has_call(node->c);
}

/* Ritorna 1 se la condizione f, senza quantificatori, è fatta di confronti
 * tra espressioni razionali nella variabile name: quelli che questo
 * capitolo sa spiegare (vedi "Che cosa si spiega"). */
static int explain_rational(const Formula *f, int name) {
    if (f->kind >= F_AND && f->kind <= F_NOT) return explain_rational(f->a, name) && (!f->b || explain_rational(f->b, name));
    if (f->kind > F_NOT) return 0;
    return sign_node_plain(f->left, name) && sign_node_plain(f->right, name) && !node_has_call(f->left) && !node_has_call(f->right);
}

/* Ritorna p, che non è il polinomio nullo, moltiplicato per la variabile
 * elevata a shift; annota un errore se il grado supera MAX_UNI. */
static Uni uni_shifted(const Uni *p, int shift) {
    Uni out = {p->degree + shift, {0}};
    if (out.degree > MAX_UNI) { fail(SIGN_LIMIT); return *p; }
    for (int i = 0; i <= p->degree; i++) out.c[i + shift] = p->c[i];
    return out;
}

/* Scrive la frazione d, nel solo atomo x, come quoziente di due polinomi a
 * coefficienti interi: d = *top / *bottom, proprio uguali, non solo con lo
 * stesso segno. Ritorna 0 se d non ha questa forma o i numeri escono dai
 * limiti.
 *
 * La valutazione dà num e den con coefficienti razionali, e con potenze
 * negative di x al posto dei denominatori fatti di sole x (capitolo 7).
 * uni_from_poly() li legge come polinomi interi: U = s p x^k, con s il
 * minimo comune multiplo dei denominatori e k lo spostamento. Quindi
 *
 *     num / den = (s_den U_num x^{k_den}) / (s_num U_den x^{k_num}),
 *
 * e i due fattori s si ritrovano da un coefficiente qualsiasi. Tolti i
 * divisori comuni a tutti i coefficienti, e reso positivo il coefficiente
 * direttivo del denominatore, la scrittura è quella che ci si aspetta:
 * 1/x - 1/(x + 1) diventa 1/(x^2 + x). */
static int explain_fraction(Rat d, int x, Uni *top, Uni *bottom) {
    const Poly part[2] = {d.num, d.den};
    Uni *whole[2] = {top, bottom};
    int shift[2] = {0, 0};
    __int128 scale[2], common = 0;
    *bottom = (Uni){0, {1}};
    if (d.num.count == 0) { *top = (Uni){-1, {0}}; return 1; }
    for (int i = 0; i < 2; i++) {
        if (!uni_from_poly(part[i], x, whole[i], &shift[i])) return 0;
        const Term *term = &part[i].term[0];
        long long exponent = (term->mono.count ? term->mono.factor[0].exp.num : 0) + shift[i];
        scale[i] = whole[i]->c[exponent] / term->coef.re.num * term->coef.re.den;
    }
    int both = shift[0] < shift[1] ? shift[0] : shift[1];
    for (int i = 0; i < 2; i++) {
        Uni scaled = uni_scaled(whole[i], scale[1 - i]);
        *whole[i] = uni_shifted(&scaled, shift[1 - i] - both);
    }
    if (failure) return 0;

    /* I divisori comuni, e il segno del denominatore. */
    for (int i = 0; i < 2; i++)
        for (int k = 0; k <= whole[i]->degree; k++) common = gcd128(common, whole[i]->c[k]);
    if (bottom->c[bottom->degree] < 0) common = -common;
    for (int i = 0; i < 2; i++)
        for (int k = 0; k <= whole[i]->degree; k++) whole[i]->c[k] /= common;
    return 1;
}

/* I punti della tabella che si sta spiegando: per ognuno il valore esatto,
 * un razionale o un numero con una radice quadrata, e la sua scrittura.
 * Valgono mentre si costruisce la spiegazione. */
static _Thread_local Rat explain_point_value[MAX_EXPLAIN_POINTS];
static _Thread_local const char *explain_point_text[MAX_EXPLAIN_POINTS];

/* Le colonne della tabella che si sta spiegando: la riga di sign_row[] di
 * ognuna, e il valore della variabile in cui si ricontrolla (il punto, o il
 * razionale scelto nell'intervallo). */
static _Thread_local int explain_row[MAX_EXPLAIN_COLUMNS];
static _Thread_local Rat explain_at[MAX_EXPLAIN_COLUMNS];

/* I fattori della tabella che si sta spiegando: per ogni punto razionale r
 * il polinomio di primo grado che si annulla in r, e ogni elemento della
 * base (18p-4) di grado almeno due. Sono gli stessi che vanno nel
 * certificato (18p-15), e ogni polinomio della tabella ne è un prodotto.
 * Di ognuno: il punto razionale di cui è il polinomio (o -1), il posto in
 * sign_base[] (o -1), il testo, l'albero riletto dal testo, e se compare in
 * un confronto spiegato. */
static _Thread_local Uni explain_factor[MAX_EXPLAIN_FACTORS];
static _Thread_local int explain_factor_point[MAX_EXPLAIN_FACTORS], explain_factor_base[MAX_EXPLAIN_FACTORS], explain_factor_used[MAX_EXPLAIN_FACTORS];
static _Thread_local const char *explain_factor_text[MAX_EXPLAIN_FACTORS];
static _Thread_local const Node *explain_factor_node[MAX_EXPLAIN_FACTORS];
static _Thread_local int explain_factors;

/* Ritorna il razionale v come frazione a 64 bit; se non ci sta annota il
 * limite e ritorna zero. */
static Rat explain_rat(Wide v) {
    if (v.num >= COEF_LIMIT || v.num <= -COEF_LIMIT || v.den >= COEF_LIMIT) { explain_broken = 1; return rat_int(0); }
    return rat_frac((Frac){(long long)v.num, (long long)v.den});
}

/* 40a. Ritorna il numero scritto in text, riletto con il lettore degli
 * enunciati: è il valore che i controlli usano al posto di quello da cui il
 * testo è stato scritto, così ciò che si controlla è ciò che si stampa. Se
 * il testo non si rilegge annota l'errore, se il conto non riesce il
 * limite; in tutti e due i casi ritorna zero. */
static Rat explain_number(const char *text) {
    Node *written = parse_expression(text);
    if (syntax_error) { syntax_error = NULL; explain_wrong = 1; return rat_int(0); }
    env_count = 0;
    Rat value = eval(written);
    if (failure) { failure = NULL; explain_broken = 1; return rat_int(0); }
    return value;
}

/* 40a. Ritorna 1 se il numero scritto in text, riletto, è proprio value;
 * altrimenti annota l'errore, o il limite se un conto non riesce. */
static int explain_number_is(const char *text, Rat value) {
    Rat gap = rat_add(explain_number(text), value, 1);
    if (failure) { failure = NULL; explain_broken = 1; }
    if (explain_broken || explain_wrong) return 0;
    if (gap.num.count != 0) explain_wrong = 1;
    return gap.num.count == 0;
}

/* Trova la scrittura e il valore esatto di ogni punto della tabella, e li
 * ricontrolla. Il valore è sempre quello che si rilegge dalla scrittura
 * (explain_number()). Per un punto razionale deve essere il razionale della
 * tabella. Un punto irrazionale deve essere la radice di un elemento della
 * base di secondo grado: la scrittura con i radicali (quadratic_latex()),
 * riletta, deve (a) annullare l'elemento e (b) stare nell'intervallo che
 * isola la radice, che distingue la radice più piccola dalla più grande:
 * uno scambio tra + e - davanti al radicale qui si vede. Ogni altro punto
 * (una radice senza scrittura, un numero con un logaritmo) ferma la
 * spiegazione. */
static void explain_points(int name) {
    if (sign_points_count > MAX_EXPLAIN_POINTS) { explain_broken = 1; return; }
    for (int k = 0; k < sign_points_count && !explain_broken && !explain_wrong; k++) {
        const Critical *point = &sign_point[k];
        char text[160] = "";
        size_t start = proof_length;
        if (point->exact) {
            put_wide(point->low);
            explain_point_text[k] = explain_piece(start);
            if (explain_broken) return;
            explain_point_value[k] = explain_rat(point->low);
            explain_number_is(explain_point_text[k], explain_point_value[k]);
            continue;
        }
        if (point->element < 0 || !quadratic_latex(&sign_base[point->element], point_is_first_root(k), text, sizeof text) || failure) { failure = NULL; explain_broken = 1; return; }
        proof_add("%s", text);
        explain_point_text[k] = explain_piece(start);
        if (explain_broken) return;

        /* Il numero riletto. */
        Rat value = explain_number(explain_point_text[k]);
        if (explain_wrong || explain_broken) return;
        explain_point_value[k] = value;

        /* (a) e (b). */
        char element[512] = "";
        int side = 0, defined = 1, above = 0, below = 0;
        uni_latex(&sign_base[point->element], name, element, sizeof element);
        Node *polynomial = parse_expression(element);
        if (syntax_error || failure) { syntax_error = failure = NULL; explain_broken = 1; return; }
        if (!explain_sign_at(polynomial, name, value, &side, &defined)) return;
        Rat low = explain_rat(point->low), high = explain_rat(point->high);
        if (explain_broken || !number_sign(rat_add(value, low, 1), &above) || !number_sign(rat_add(high, value, 1), &below)) { failure = NULL; explain_broken = 1; return; }
        if (!defined || side != 0 || above <= 0 || below <= 0) explain_wrong = 1;
    }
}

/* Scrive che cosa indica la riga row della tabella, nella variabile name:
 * "x = 2" per un punto, "-3 < x < 2", "x < -3" o "x > 2" per un
 * intervallo. Chi chiama ha già escluso la tabella senza punti. */
static void put_column(int row, int name) {
    if (row % 2) { proof_add("%c = %s", name, explain_point_text[row / 2]); return; }
    if (row == 0) { proof_add("%c < %s", name, explain_point_text[0]); return; }
    if (row / 2 == sign_points_count) { proof_add("%c > %s", name, explain_point_text[row / 2 - 1]); return; }
    proof_add("%s < %c < %s", explain_point_text[row / 2 - 1], name, explain_point_text[row / 2]);
}

/* Mette in ordine le colonne della tabella: una per ogni riga di sign_row[]
 * che sta nell'insieme su cui varia la variabile name, con il valore in cui
 * la si ricontrolla e la sua intestazione.
 *
 * Anche le intestazioni si ricontrollano (40a): ognuna, riletta come
 * condizione, deve valere nel valore della sua colonna e in nessuno delle
 * altre. Un < al posto di un >, o due punti scambiati, qui si vedono. */
static void explain_columns(int name) {
    explanation.columns = 0;
    for (int row = 0; row < sign_rows && !explain_broken; row++) {
        if (!sign_row[row].inside) continue;
        if (explanation.columns == MAX_EXPLAIN_COLUMNS) { explain_broken = 1; return; }
        int column = explanation.columns++;
        size_t start = proof_length;
        explain_row[column] = row;
        explain_at[column] = row % 2 ? explain_point_value[row / 2] : explain_rat(sign_row[row].sample);
        explanation.head[column] = NULL;
        if (sign_points_count == 0) continue;
        put_column(row, name);
        explanation.head[column] = explain_piece(start);
    }

    /* Una tabella senza colonne non spiega nulla. */
    if (explanation.columns == 0) explain_broken = 1;
    for (int column = 0; column < explanation.columns && sign_points_count && !explain_broken; column++) {
        const Formula *written = condition_reread(explanation.head[column]);
        if (!written) { explain_wrong = 1; return; }
        for (int other = 0; other < explanation.columns; other++) {
            int inside = explain_holds(written, name, explain_at[other]);
            if (explain_broken) return;
            if (inside != (other == column)) { explain_wrong = 1; return; }
        }
    }
}

/* Scrive la condizione f com'era scritta (put_written()) e ne ritorna il
 * testo, dopo averlo ricontrollato: riletto con il lettore degli enunciati,
 * in ogni colonna della tabella deve valere esattamente quando la tabella
 * del motore dice che f vale. name è la variabile. */
static const char *explain_condition(const Formula *f, int name) {
    size_t start = proof_length;
    put_written(f);
    const char *text = explain_piece(start);
    if (explain_broken) return text;
    const Formula *written = condition_reread(text);
    if (!written) { explain_wrong = 1; return text; }
    for (int column = 0; column < explanation.columns; column++) {
        int again = explain_holds(written, name, explain_at[column]);
        if (explain_broken) break;
        if (again != sign_truth(f, sign_row[explain_row[column]].sign)) { explain_wrong = 1; break; }
    }
    return text;
}

/* Elenca i fattori della tabella (vedi explain_factor[]), ognuno con il suo
 * testo e con l'albero che se ne rilegge. */
static void explain_factor_list(int name) {
    explain_factors = 0;
    for (int pass = 0; pass < 2; pass++)
        for (int k = 0; k < (pass ? sign_bases : sign_points_count); k++) {
            /* Prima i punti razionali, poi gli elementi di grado almeno due. */
            if (pass ? sign_base[k].degree < 2 : !sign_point[k].exact) continue;
            if (explain_factors == MAX_EXPLAIN_FACTORS) { explain_broken = 1; return; }
            int j = explain_factors++;
            size_t start = proof_length;
            explain_factor[j] = pass ? sign_base[k] : (Uni){1, {-sign_point[k].low.num, sign_point[k].low.den}};
            explain_factor_point[j] = pass ? -1 : k;
            explain_factor_base[j] = pass ? k : -1;
            explain_factor_used[j] = 0;
            put_uni(&explain_factor[j], name);
            explain_factor_text[j] = explain_piece(start);
            if (failure || explain_broken) { failure = NULL; explain_broken = 1; return; }
            explain_factor_node[j] = parse_expression(explain_factor_text[j]);
            if (syntax_error) { syntax_error = NULL; explain_wrong = 1; return; }
        }
}

/* Scompone p, che non è il polinomio nullo, nei fattori della tabella:
 * p = *constant per il prodotto degli explain_factor[j] elevati a power[j].
 * Ritorna 0 se avanza qualcosa che non è una costante: p non è di questa
 * tabella. I fattori hanno coefficienti senza divisori comuni, quindi ogni
 * divisione esatta si fa tra interi (uni_divide()). */
static int explain_split(Uni p, __int128 *constant, int *power) {
    for (int j = 0; j < explain_factors; j++) {
        Uni quotient;
        power[j] = 0;
        while (p.degree >= explain_factor[j].degree && uni_divide(&p, &explain_factor[j], &quotient)) {
            p = quotient;
            power[j]++;
        }
    }
    *constant = p.degree == 0 ? p.c[0] : 0;
    return p.degree == 0 && !failure;
}

/* Scrive constant per il prodotto dei fattori elevati a power[]: prima il
 * numero (solo il segno, se è -1; nulla, se è 1 e c'è almeno un fattore),
 * poi i fattori di un solo termine, come x, poi gli altri, tra parentesi
 * quando non sono soli. Ciò che scrive si rilegge come quel prodotto.
 *
 * Ritorna 1 se non c'è stato nulla da raccogliere: il prodotto è un numero,
 * oppure un solo fattore alla prima potenza con davanti 1 o, se il fattore
 * è di un solo termine, un numero qualsiasi (3x). Chi chiama lo usa per non
 * registrare come passo una scomposizione che non scompone. */
static int put_product(__int128 constant, const int *power) {
    int count = 0, plain = 1;
    for (int j = 0; j < explain_factors; j++) count += power[j];
    if (constant > LLONG_MAX || constant < -LLONG_MAX) { explain_broken = 1; return 1; }
    if (count == 0 || (constant != 1 && constant != -1)) proof_add("%lld", (long long)constant);
    else if (constant == -1) proof_add("-");
    for (int pass = 0; pass < 2; pass++)
        for (int j = 0; j < explain_factors; j++) {
            int terms = 0;
            for (int i = 0; i <= explain_factor[j].degree; i++) terms += explain_factor[j].c[i] != 0;
            if (power[j] == 0 || (terms == 1) != (pass == 0)) continue;
            if (count > 1 || (constant != 1 && terms > 1)) plain = 0;
            proof_add(terms > 1 && (count > 1 || constant != 1) ? "\\left(%s\\right)" : "%s", explain_factor_text[j]);
            if (power[j] > 1) proof_add("^{%d}", power[j]);
        }
    return plain;
}

/* Ritorna 1 se node è un monomio scritto per esteso: un numero, una
 * lettera, una sua potenza con l'esponente scritto, o un numero per una di
 * queste, anche con il segno meno davanti. */
static int node_monomial(const Node *node) {
    if (node->kind == N_NEG) return node_monomial(node->a);
    if (node->kind == N_MUL) return node->a->kind == N_NUM && node->b->kind != N_NUM && node_monomial(node->b);
    if (node->kind == N_POW) return node->a->kind == N_VAR && node->b->kind == N_NUM;
    return node->kind == N_NUM || node->kind == N_VAR;
}

/* Ritorna 1 se node è già scritto come un prodotto o un quoziente di
 * polinomi, ognuno una somma di monomi: x^{2} - 5x + 6, \frac{x - 2}{x + 3},
 * (x - 1)(x + 2)^{2}. Di un'espressione così non c'è nulla da svolgere né
 * da mettere a denominatore comune. */
static int node_written_out(const Node *node) {
    if (node->kind == N_ADD || node->kind == N_SUB) {
        /* Una somma: di monomi, o di somme di monomi. */
        const Node *part[2] = {node->a, node->b};
        for (int i = 0; i < 2; i++)
            if (!node_monomial(part[i]) && !((part[i]->kind == N_ADD || part[i]->kind == N_SUB) && node_written_out(part[i]))) return 0;
        return 1;
    }
    if (node->kind == N_MUL || node->kind == N_DIV) return node_written_out(node->a) && node_written_out(node->b);
    if (node->kind == N_POW && node->b->kind == N_NUM) return node_written_out(node->a);
    if (node->kind == N_NEG) return node_written_out(node->a);
    return node_monomial(node);
}

/* Ritorna 1 se i due testi sono la stessa formula a meno di come è
 * composta: senza contare gli spazi e i \cdot, che put_node() mette tra due
 * parentesi e put_product() no. */
static int formula_text_same(const char *a, const char *b) {
    for (;;) {
        for (int skipped = 1; skipped; ) {
            skipped = 0;
            if (*a == ' ') { a++; skipped = 1; }
            if (*b == ' ') { b++; skipped = 1; }
            if (strncmp(a, "\\cdot", 5) == 0) { a += 5; skipped = 1; }
            if (strncmp(b, "\\cdot", 5) == 0) { b += 5; skipped = 1; }
        }
        if (*a != *b) return 0;
        if (!*a) return 1;
        a++;
        b++;
    }
}

/* Ciò che la catena di un confronto lascia a chi fa la tabella. */
typedef struct {
    const Formula *source;  /* il confronto */
    ExplainStep *opening;   /* il suo passo EXPLAIN_COMPARISON */
    const char *written;    /* il confronto com'è scritto */
    const char *last;       /* l'ultima forma della differenza dei membri */
    const Node *difference; /* la differenza dei membri, riletta dal testo */
    int sign;               /* il segno del numero davanti ai fattori; 0 se la
                               differenza è zero */
    int power[MAX_EXPLAIN_FACTORS];  /* quante volte ogni fattore compare nella
                               frazione, tra numeratore e denominatore: per
                               il segno conta solo se è pari o dispari */
    int below[MAX_EXPLAIN_FACTORS];  /* 1 se il fattore sta al denominatore:
                               dove si annulla la frazione non ha un valore */
} ExplainChain;

/* Registra la catena del confronto f, il numero group, nella variabile name
 * di atomo x: il confronto com'è scritto, la differenza dei due membri
 * (EXPLAIN_MOVE), la stessa come una sola frazione (EXPLAIN_COMBINE) e con
 * numeratore e denominatore scomposti nei fattori della tabella
 * (EXPLAIN_FACTOR). Un passo che non fa nulla non si registra: il primo se
 * un membro è già 0, il secondo se la differenza è già un prodotto o un
 * quoziente di polinomi scritti per esteso, il terzo se non c'è nulla da
 * raccogliere. Ogni forma scritta deve rileggersi uguale alla differenza che
 * calcola la valutazione (explain_equals()). Riempie *chain. */
static void explain_chain(const Formula *f, int group, int name, int x, ExplainChain *chain) {
    const Node *first = f->swapped ? f->right : f->left, *second = f->swapped ? f->left : f->right;
    int direct = second->kind == N_NUM && second->value == 0;
    const char *relation = explain_relation(f);
    memset(chain, 0, sizeof *chain);
    chain->source = f;

    /* Il confronto com'è scritto, riletto e confrontato con la tabella. */
    chain->written = explain_condition(f, name);
    chain->opening = explain_step(EXPLAIN_COMPARISON, group);
    chain->opening->text[0] = chain->written;
    if (explain_wrong || explain_broken) return;

    /* La differenza dei due membri, come la calcola la valutazione: è il
     * termine di confronto di ogni forma scritta. */
    env_count = 0;
    Rat gap = rat_add(eval(first), eval(second), 1);
    if (failure) { failure = NULL; explain_broken = 1; return; }

    /* Tutto a un membro. Se l'altro è già 0 la differenza è il primo. */
    size_t start = proof_length;
    put_node(first, direct ? 0 : 1);
    if (!direct) { proof_add(" - "); put_node(second, 2); }
    chain->last = explain_piece(start);
    if (explain_broken || !explain_equals(chain->last, gap)) return;
    chain->difference = parse_expression(chain->last);
    if (!direct) {
        ExplainStep *step = explain_step(EXPLAIN_MOVE, group);
        step->text[0] = chain->last;
        step->text[1] = relation;
    }

    /* Una sola frazione di polinomi. Il passo si salta se la differenza è
     * già scritta così: svolgere (x - 1)(x + 2) per poi scomporlo di nuovo
     * non è un passaggio che si farebbe alla lavagna. */
    Uni top, bottom;
    char above[512] = "", below[512] = "";
    if (!explain_fraction(gap, x, &top, &bottom) || failure) { failure = NULL; explain_broken = 1; return; }
    int whole = bottom.degree == 0 && bottom.c[0] == 1;
    uni_latex(&top, name, above, sizeof above);
    uni_latex(&bottom, name, below, sizeof below);
    if (failure) { failure = NULL; explain_broken = 1; return; }
    start = proof_length;
    proof_add(whole ? "%s" : "\\frac{%s}{%s}", above, below);
    const char *combined = explain_piece(start);
    if (explain_broken) return;
    if (!node_written_out(chain->difference) && !formula_text_same(combined, chain->last)) {
        if (!explain_equals(combined, gap)) return;
        ExplainStep *step = explain_step(EXPLAIN_COMBINE, group);
        step->text[0] = chain->last = combined;
        step->text[1] = relation;
        step->flag = !whole;
    }

    /* I fattori. Una differenza che è zero non ne ha. Il passo si salta se
     * non c'è nulla da raccogliere, o se la forma di prima è già questa. */
    if (top.degree < 0) return;
    __int128 lead[2];
    int power[2][MAX_EXPLAIN_FACTORS], plain = 1;
    if (!explain_split(top, &lead[0], power[0]) || !explain_split(bottom, &lead[1], power[1])) { failure = NULL; explain_broken = 1; return; }
    whole = lead[1] == 1;
    for (int j = 0; j < explain_factors; j++) {
        chain->power[j] = power[0][j] + power[1][j];
        chain->below[j] = power[1][j] > 0;
        if (chain->power[j]) explain_factor_used[j] = 1;
        if (power[1][j]) whole = 0;
    }
    chain->sign = lead[0] > 0 ? 1 : -1;
    start = proof_length;
    if (!whole) proof_add("\\frac{");
    plain &= put_product(lead[0], power[0]);
    if (!whole) { proof_add("}{"); plain &= put_product(lead[1], power[1]); proof_add("}"); }
    const char *factored = explain_piece(start);
    if (explain_broken || plain || formula_text_same(factored, chain->last)) return;
    if (!explain_equals(factored, gap)) return;
    ExplainStep *step = explain_step(EXPLAIN_FACTOR, group);
    step->text[0] = chain->last = factored;
    step->text[1] = relation;
    step->flag = !whole;
}

/* Ritorna 1 se il polinomio di secondo grado q non ha radici reali: il suo
 * discriminante b^2 - 4ac è negativo. È un conto a sé, che non passa dalle
 * catene di Sturm con cui la tabella ha contato le radici (18p-3). */
static int quadratic_never_zero(const Uni *q) {
    __int128 square, product;
    if (q->degree != 2 || __builtin_mul_overflow(q->c[1], q->c[1], &square) || __builtin_mul_overflow(q->c[2], q->c[0], &product) ||
        __builtin_mul_overflow(product, (__int128)4, &product)) return 0;
    return square < product;
}

/* Registra gli zeri di ogni fattore che compare in un confronto spiegato
 * (EXPLAIN_ZERO), nella variabile name. certified dice se checker.c ha
 * accettato il certificato della tabella.
 *
 * Gli zeri sono i punti della tabella: per un fattore di primo grado il suo
 * punto razionale, per un elemento della base le sue radici. Ogni zero
 * scritto si ricontrolla sostituendolo nel fattore riletto. Che non ce ne
 * siano altri: un polinomio di grado d ha al più d radici, e i fattori con
 * radici qui hanno grado uno, con una radice, o due, con due. Per un
 * fattore senza radici reali vedi 40a; il suo segno lo aggiunge
 * explain_table(). */
static void explain_zeros(int name, int certified) {
    for (int j = 0; j < explain_factors && !explain_broken && !explain_wrong; j++) {
        if (!explain_factor_used[j]) continue;
        ExplainStep *step = explain_step(EXPLAIN_ZERO, 0);
        step->text[0] = explain_factor_text[j];
        for (int k = 0; k < sign_points_count; k++) {
            const Critical *point = &sign_point[k];
            int side = 0, defined = 1;
            if (point->exact ? explain_factor_point[j] != k : point->element != explain_factor_base[j]) continue;
            if (step->count == 2) { explain_wrong = 1; return; }
            if (!explain_sign_at(explain_factor_node[j], name, explain_point_value[k], &side, &defined)) return;
            if (!defined || side != 0) { explain_wrong = 1; return; }
            step->text[++step->count] = explain_point_text[k];
        }
        if (step->count != (explain_factor[j].degree == 1 ? 1 : step->count ? 2 : 0) || (step->count && explain_factor[j].degree > 2)) { explain_wrong = 1; return; }

        /* Mai zero: il segno, lo stesso ovunque, lo mette explain_table(),
         * che lo legge dalla riga del fattore. */
        if (step->count == 0 && !quadratic_never_zero(&explain_factor[j]) && !certified) { explain_broken = 1; return; }
    }
}

/* Ritorna il segno che la tabella del motore dà al fattore numero j nella
 * riga row: zero nel suo punto, altrimenti il suo segno nel valore della
 * riga. In una radice irrazionale di un altro elemento il valore della riga
 * è il punto medio dell'intervallo che la isola, e il segno lì è quello
 * nella radice (18p-5). */
static int explain_factor_sign(int j, int row) {
    if (row % 2) {
        const Critical *point = &sign_point[row / 2];
        if (point->exact ? explain_factor_point[j] == row / 2 : point->element == explain_factor_base[j]) return 0;
    }
    return uni_sign_at(&explain_factor[j], sign_row[row].sample);
}

/* Riempie la tabella della spiegazione, nella variabile name: una riga per
 * ogni fattore usato, poi per ogni confronto il segno della differenza dei
 * membri e se il confronto vale, poi la condizione shown se non è un solo
 * confronto, e per un'equivalenza body il suo secondo membro e se i due
 * dicono lo stesso. chain[] sono le catene dei `count` confronti, claim il
 * testo del secondo membro dell'equivalenza.
 *
 * Ogni casella è scritta con ciò che la tabella del motore ha usato (i
 * segni dei suoi polinomi, sign_compare(), sign_truth()) e ricontrollata
 * sostituendo il valore della colonna nel testo riletto (40a). In più il
 * prodotto dei segni dei fattori deve dare il segno della frazione, e dove
 * un fattore del denominatore è zero la frazione non deve avere un valore:
 * è ciò che lega la scomposizione alla tabella. Infine annota, nel passo
 * che apre ogni confronto, in quali colonne non ha un valore. */
static void explain_table(const ExplainChain *chain, int count, const Formula *shown, const Formula *body, const char *claim, int name) {
    int place[MAX_EXPLAIN_FACTORS] = {0};
    explanation.lines = 0;

    /* I fattori. */
    for (int j = 0; j < explain_factors && !explain_broken && !explain_wrong; j++) {
        if (!explain_factor_used[j]) continue;
        ExplainLine *line = explain_line(EXPLAIN_LINE_FACTOR, 0, explain_factor_text[j]);
        place[j] = explanation.lines - 1;
        for (int column = 0; column < explanation.columns; column++) {
            int side = 0, defined = 1, engine = explain_factor_sign(j, explain_row[column]);
            if (failure) { failure = NULL; explain_broken = 1; return; }
            if (!explain_sign_at(explain_factor_node[j], name, explain_at[column], &side, &defined)) return;
            if (!defined || side != engine) { explain_wrong = 1; return; }
            line->cell[column] = (signed char)engine;
        }

        /* Il passo di un fattore che non si annulla mai ne dice il segno:
         * è quello di questa riga, che deve essere lo stesso in ogni
         * colonna. */
        for (int s = 0; s < explanation.steps; s++) {
            ExplainStep *step = &explanation.step[s];
            if (step->kind != EXPLAIN_ZERO || step->count || step->text[0] != line->label) continue;
            step->flag = line->cell[0];
            for (int column = 0; column < explanation.columns; column++)
                if (line->cell[column] == 0 || line->cell[column] != step->flag) { explain_wrong = 1; return; }
        }
    }

    /* I confronti. */
    for (int i = 0; i < count && !explain_broken && !explain_wrong; i++) {
        const Formula *f = chain[i].source;
        size_t start = proof_length;
        int missing = 0, repeated = 0;

        /* Se la differenza dei membri è un fattore solo, la sua riga c'è
         * già tra quelle dei fattori: non la si scrive due volte. I
         * controlli della riga si fanno lo stesso, su una riga di riserva. */
        static _Thread_local ExplainLine unwritten;
        for (int j = 0; j < explain_factors; j++) repeated |= explain_factor_used[j] && formula_text_same(chain[i].last, explain_factor_text[j]);
        ExplainLine *value = repeated ? &unwritten : explain_line(EXPLAIN_LINE_VALUE, i + 1, chain[i].last);
        ExplainLine *truth = explain_line(EXPLAIN_LINE_COMPARISON, i + 1, chain[i].written);
        if (explain_broken) return;
        for (int column = 0; column < explanation.columns; column++) {
            const int *sign = sign_row[explain_row[column]].sign;
            int defined = 1, engine = sign_compare(f, sign, &defined) * (f->swapped ? -1 : 1), holds = sign_truth(f, sign);
            int side = 0, there = 1, product = chain[i].sign, divided = 0;
            if (!explain_sign_at(chain[i].difference, name, explain_at[column], &side, &there)) return;
            for (int j = 0; j < explain_factors; j++) {
                int factor = chain[i].power[j] ? explanation.line[place[j]].cell[column] : 1;
                if (chain[i].below[j] && factor == 0) divided = 1;
                if (chain[i].power[j] % 2 || factor == 0) product *= factor;
            }
            if (there != defined || (defined && (side != engine || product != engine)) || (divided && defined) ||
                holds != (defined && explain_relation_holds(f, side))) { explain_wrong = 1; return; }
            value->cell[column] = (signed char)(defined ? engine : EXPLAIN_NO_VALUE);
            truth->cell[column] = (signed char)holds;
            if (defined) continue;
            proof_add(missing++ ? ",\\ %s" : "%s", explanation.head[column] ? explanation.head[column] : "");
        }
        chain[i].opening->count = missing;
        chain[i].opening->text[1] = explain_piece(start);
    }

    /* La condizione, e per un'equivalenza il suo secondo membro. */
    const Formula *part[3] = {count > 1 || shown != chain[0].source ? shown : NULL, body != shown ? body->b : NULL, body != shown ? body : NULL};
    static const ExplainLineKind kind[3] = {EXPLAIN_LINE_CONDITION, EXPLAIN_LINE_CLAIM, EXPLAIN_LINE_AGREE};
    for (int p = 0; p < 3 && !explain_broken && !explain_wrong; p++) {
        if (!part[p]) continue;
        ExplainLine *line = explain_line(kind[p], 0, p == 1 ? claim : NULL);
        for (int column = 0; column < explanation.columns; column++) {
            int engine = sign_truth(part[p], sign_row[explain_row[column]].sign), again = explain_holds(part[p], name, explain_at[column]);
            if (explain_broken) return;
            if (engine != again) { explain_wrong = 1; return; }
            line->cell[column] = (signed char)engine;
        }
    }
}

/* Registra un valore di prova (EXPLAIN_TEST) per ogni confronto e per ogni
 * colonna che è un intervallo: i due membri calcolati nel razionale scelto,
 * e se lì il confronto vale. chain[] sono le catene dei `count` confronti,
 * name la variabile.
 *
 * I due valori vengono dal conto esatto del capitolo 11, e ognuno deve
 * stare nell'intervallo che il capitolo 24 calcola per lo stesso membro
 * nello stesso punto: due conti che non hanno nulla in comune. Il confronto
 * tra i due numeri deve dare la verità che la tabella ha in quella colonna.
 * Dove un membro non ha un valore razionale il valore di prova non si
 * scrive. */
static void explain_tests(const ExplainChain *chain, int count, int name) {
    for (int column = 0; column < explanation.columns; column++) {
        int row = explain_row[column];
        Wide sample = sign_row[row].sample;
        if (row % 2) continue;
        for (int i = 0; i < count && !explain_broken && !explain_wrong; i++) {
            const Formula *f = chain[i].source;
            const Node *side[2] = {f->swapped ? f->right : f->left, f->swapped ? f->left : f->right};
            Num value[2];
            int known = 1;
            for (int s = 0; s < 2 && known; s++) {
                int nowhere = 0, apart = 0;
                env_count = 0;
                env_push(name, explain_at[column]);
                known = rat_number(eval(side[s]), &value[s]) && !failure && value[s].im.num == 0;
                env_count = 0;
                failure = NULL;
                if (!known) break;
                Range enclosure = node_range(side[s], name, range_ratio(sample.num, sample.den), &nowhere);
                if (nowhere || (range_known(enclosure) && range_side(range_sub(enclosure, range_ratio(value[s].re.num, value[s].re.den)), &apart) && apart != 0)) { explain_wrong = 1; return; }
            }
            if (!known) continue;
            int holds = explain_relation_holds(f, frac_cmp(value[0].re, value[1].re));
            if (holds != sign_truth(f, sign_row[row].sign)) { explain_wrong = 1; return; }
            /* Il valore scelto e i due risultati, scritti e riletti: ciò che
             * si stampa deve essere ciò con cui si è fatto il conto. */
            ExplainStep *step = explain_step(EXPLAIN_TEST, i + 1);
            size_t start = proof_length;
            put_wide(sample);
            step->text[0] = explain_piece(start);
            if (explain_broken || !explain_number_is(step->text[0], explain_at[column])) return;
            for (int s = 0; s < 2; s++) {
                start = proof_length;
                put_frac(value[s].re);
                step->text[1 + s] = explain_piece(start);
                if (explain_broken || !explain_number_is(step->text[1 + s], rat_frac(value[s].re))) return;
            }
            step->text[3] = explain_relation(f);
            step->flag = holds;
        }
    }
}

/* Registra la risposta (EXPLAIN_ANSWER) dell'enunciato che il verdetto
 * *verdict ha deciso, leggendola dall'ultima riga della tabella: le
 * soluzioni scritte, oppure la prima colonna che smentisce un "per ogni" o
 * conferma un "esiste". Che la risposta sia quella del verdetto è l'ultimo
 * controllo. */
static void explain_answer(const Verdict *verdict) {
    const ExplainLine *last = &explanation.line[explanation.lines - 1];
    ExplainStep *step = explain_step(EXPLAIN_ANSWER, 0);
    int every = explanation.request == EXPLAIN_FORALL, decided = -1, held = 0;
    for (int column = 0; column < explanation.columns; column++) {
        held += last->cell[column];
        if (decided < 0 && explanation.request != EXPLAIN_SOLVE && last->cell[column] != every) decided = column;
    }
    if (explanation.request == EXPLAIN_SOLVE) {
        step->text[0] = verdict->detail;
        step->count = strncmp(verdict->detail, "\\forall", 7) == 0 ? 1 : strncmp(verdict->detail, "\\nexists", 8) == 0 ? 2 : 0;
        if ((step->count == 1) != (held == explanation.columns) || (step->count == 2) != (held == 0)) explain_wrong = 1;
        return;
    }
    step->flag = every ? decided < 0 : decided >= 0;
    step->count = decided >= 0;
    step->text[0] = decided >= 0 ? explanation.head[decided] : NULL;
    if (step->flag != (verdict->outcome == PROVED)) explain_wrong = 1;
}

/* 40. Registra in `explanation` la spiegazione dell'enunciato thesis, che
 * decide_by_signs() ha appena deciso con il verdetto *verdict (e
 * sign_certify() fatto ricontrollare): lo stato della tabella dei segni è
 * ancora quello. Non cambia il verdetto. Se l'enunciato non è tra quelli
 * che si sanno spiegare (vedi in testa al capitolo), o un limite lo
 * impedisce, la spiegazione resta vuota; se un controllo di 40a fallisce
 * resta vuota e unjustified_steps sale.
 *
 * Tutto ciò che il conto lascia in giro (atomi, memoria dell'arena, un
 * errore annotato, i segnali di memoria e pila finite) viene rimesso
 * com'era: chi ha chiesto il verdetto non deve accorgersi che dopo c'è
 * stata una spiegazione. */
void explain_signs(const Formula *thesis, const Verdict *verdict) {
    static _Thread_local ExplainChain chain[MAX_PANELS];
    const Formula *panel[MAX_PANELS + 1];
    int negated, count = 0;
    const Formula *q = without_negations(thesis, &negated);
    explanation.steps = 0;
    if ((verdict->outcome != PROVED && verdict->outcome != REFUTED && verdict->outcome != SOLVED) || !verdict->proof) return;
    if (negated || trig_on || spaces || kappas || !explain_rational(q->a, q->variable)) return;
    const Formula *body = q->a, *shown = body->kind == F_IFF && q->kind != F_SOLVE ? body->a : body;
    int name = q->variable, x = atom_var(name);
    comparisons_collect(shown, panel, &count);
    if (count == 0 || count > MAX_PANELS) return;

    /* Lo stato da rimettere com'era. */
    Scratch mark = scratch_mark();
    const char *was = failure;
    int memory = work_allocation_failed, stack = stack_exhausted;
    failure = NULL;
    explain_wrong = explain_broken = 0;
    explain_capture(1);

    /* Che cosa si chiede. */
    explanation.variable = name;
    explanation.request = q->kind == F_SOLVE ? EXPLAIN_SOLVE : q->kind == F_FORALL ? EXPLAIN_FORALL : EXPLAIN_EXISTS;
    explanation.equivalence = shown != body;
    explanation.comparisons = count;
    ExplainStep *ask = explain_step(EXPLAIN_ASK, 0);
    size_t start = proof_length;
    put_numbers(&q->numbers);
    ask->text[1] = explain_piece(start);

    /* I punti e le colonne della tabella, e con quelle la condizione
     * com'è scritta, che si ricontrolla colonna per colonna; poi i fattori,
     * le catene, gli zeri, la tabella, i valori di prova e la risposta.
     * Dopo ogni pezzo si guarda se si può proseguire: ognuno conta su
     * quelli prima. */
    explain_points(name);
    if (!explain_wrong && !explain_broken) explain_columns(name);
    if (!explain_wrong && !explain_broken) ask->text[0] = explain_condition(shown, name);
    if (!explain_wrong && !explain_broken && shown != body) ask->text[2] = explain_condition(body->b, name);
    if (!explain_wrong && !explain_broken) explain_factor_list(name);
    for (int i = 0; i < count && !explain_wrong && !explain_broken; i++) explain_chain(panel[i], i + 1, name, x, &chain[i]);
    if (!explain_wrong && !explain_broken) explain_zeros(name, verdict->certificate != NULL);
    if (!explain_wrong && !explain_broken) {
        ExplainStep *points = explain_step(EXPLAIN_POINTS, 0);
        start = proof_length;
        for (int column = 0; column < explanation.columns; column++)
            if (explain_row[column] % 2) proof_add(points->count++ ? ",\\ %s" : "%s", explain_point_text[explain_row[column] / 2]);
        points->text[0] = explain_piece(start);
        explain_step(EXPLAIN_TABLE, 0);
        explain_table(chain, count, shown, body, ask->text[2], name);
    }
    if (!explain_wrong && !explain_broken) explain_tests(chain, count, name);
    if (!explain_wrong && !explain_broken) explain_answer(verdict);

    /* Un anello che non regge: niente spiegazione, e il contatore sale. */
    if (failure || work_allocation_failed != memory || stack_exhausted != stack) explain_broken = 1;
    if (explain_wrong) unjustified_steps++;
    if (explain_wrong || explain_broken) explanation.steps = 0;
    explain_capture(0);
    syntax_error = NULL;
    failure = was;
    work_allocation_failed = memory;
    stack_exhausted = stack;
    scratch_drop(mark);
}

/* 40b. L'INDUZIONE: I PRIMI VALORI E IL PASSO SVOLTO
 *
 * A che cosa serve. "La somma dei primi n interi è n(n + 1)/2" è
 * un'affermazione su infiniti numeri, e la dimostrazione per induzione
 * (capitolo 13) la chiude con un caso base e un passo. Chi la legge per la
 * prima volta ha bisogno di due cose prima: vedere che cosa si afferma, su
 * dei numeri, e vedere il passo svolto come un conto. Qui si registrano:
 *
 *   - l'enunciato, e i suoi primi EXPLAIN_VALUES casi: i due membri
 *     calcolati per n = n0, n0 + 1, ..., una riga per caso
 *     (EXPLAIN_VALUE), e gli stessi in un grafico;
 *   - il caso base, con i due membri scritti con il numero al posto di n
 *     (EXPLAIN_BASE), e l'ipotesi induttiva (EXPLAIN_HYPOTHESIS);
 *   - il passo, quando l'enunciato ha la forma più comune: un membro è una
 *     somma o un prodotto fino a n, l'altro una formula senza somme. Allora
 *     il membro con la somma, scritto per n + 1, è una catena di tre
 *     passaggi (EXPLAIN_TARGET, poi tre EXPLAIN_REWRITE): si stacca
 *     l'ultimo termine, si mette la formula al posto della somma fino a n
 *     (è l'ipotesi), si fanno i conti; e l'altro membro per n + 1, fatti i
 *     conti, è la stessa espressione. È ciò che fa step_holds() (13b):
 *     ricava la somma dall'ipotesi, la sostituisce in D(n + 1), e resta il
 *     polinomio nullo. Con le altre forme (una somma in tutti e due i
 *     membri, o dentro un'espressione) il passo resta nella dimostrazione
 *     scritta dal capitolo 13, che il documento riporta sotto.
 *
 * I controlli sono quelli del capitolo 13 per le formule di una
 * dimostrazione (13g, reread_equal()): due formule scritte si rileggono dal
 * testo con il lettore degli enunciati, come se le avesse scritte l'utente,
 * e la loro uguaglianza passa per la verifica con i numeri (13e) dal caso
 * base in su. Vale per ogni riga dei primi valori (il membro con il numero
 * al posto di n, e il valore scritto accanto), per l'enunciato, e per ogni
 * anello della catena del passo: anche quello che usa l'ipotesi, perché
 * l'enunciato è dimostrato, e quindi i due testi hanno lo stesso valore per
 * ogni n. In più, in ogni riga i due membri devono dare lo stesso numero:
 * sono due espressioni diverse, calcolate ognuna per conto suo, e se un
 * enunciato dato per dimostrato avesse una riga che non torna, qui si
 * vedrebbe.
 *
 * Il grafico. I valori del primo membro come punti, quelli del secondo
 * come vertici di una spezzata (induction_figure() dice perché). Vengono
 * dai valori esatti della tabella, e i numeri in virgola mobile servono,
 * come in 18q, a metterli sulla pagina. Lo si costruisce solo insieme alla
 * spiegazione: il documento asciutto non lo ha. Non ha chiesto primitive
 * nuove a plot.c.
 *
 * Che cosa non c'è ancora: gli enunciati con un parametro (i valori non
 * sono numeri), le disuguaglianze (capitolo 25: lì il grafico direbbe di
 * più, un membro sopra l'altro), le successioni per ricorrenza (capitolo
 * 26), e l'induzione usata dentro un enunciato con quantificatori (18n).
 */

#define EXPLAIN_VALUES 6  /* i primi casi di un enunciato per induzione che si mostrano */

/* Chiude il pezzo di testo cominciato in start, come explain_piece(), e
 * mette in *span il posto che occupa nel deposito: serve a chi lo deve far
 * rileggere con reread_equal() (13g), che lavora sui pezzi del testo in
 * corso. */
static const char *explain_span(size_t start, Span *span) {
    *span = (Span){start, proof_length};
    return explain_piece(start);
}

/* Ritorna 1 se nell'espressione node compare una somma o un prodotto
 * scritti con \sum o \prod. */
static int node_has_bigop(const Node *node) {
    if (!node) return 0;
    return node->kind == N_BIGOP || node_has_bigop(node->a) || node_has_bigop(node->b) || node_has_bigop(node->c);
}

/* Costruisce in `figure` il grafico dei primi valori di un enunciato per
 * induzione: per ogni n da base, per `rows` casi, il valore del primo
 * membro, un punto, e quello del secondo, un vertice di una spezzata.
 * value[i][s] è il valore del membro s nel caso numero i. Se manca la
 * memoria il grafico non c'è.
 *
 * Perché un punto e una spezzata. I due membri hanno gli stessi valori:
 * due punti uguali starebbero uno sopra l'altro, e se ne vedrebbe uno. Così
 * invece si vede ciò che la tabella dice: ogni punto sta sulla spezzata. La
 * spezzata unisce i valori solo per farli riconoscere: tra un n e il
 * successivo non dice nulla. I double servono solo a mettere punti e
 * vertici sulla pagina. */
static void induction_figure(long long base, Frac value[][2], int rows) {
    static _Thread_local char text[EXPLAIN_VALUES][24];
    const char *label[EXPLAIN_VALUES];
    double at[EXPLAIN_VALUES], height[2][EXPLAIN_VALUES], low = 0, high = 0;
    figure = pl_figure(6.4, 3.0);
    PlAxes *axes = pl_add_axes(figure, 1);
    if (!axes) { pl_close(figure); figure = NULL; return; }
    for (int i = 0; i < rows; i++) {
        at[i] = (double)(base + i);
        snprintf(text[i], sizeof text[i], "%lld", base + i);
        label[i] = text[i];
        for (int s = 0; s < 2; s++) {
            double y = height[s][i] = (double)value[i][s].num / (double)value[i][s].den;
            if ((i == 0 && s == 0) || y < low) low = y;
            if ((i == 0 && s == 0) || y > high) high = y;
        }
    }
    /* Senza legenda: starebbe in alto a destra, proprio sull'ultimo punto
     * di una successione che cresce. Che cosa sono punti e spezzata lo dice
     * il titolo. */
    pl_plot(axes, at, height[1], rows, PL_ORANGE, 1.5, NULL);
    for (int i = 0; i < rows; i++) pl_marker(axes, at[i], height[0][i], PL_BLUE, 1);

    /* Un margine attorno ai punti, anche se stanno tutti alla stessa
     * altezza. */
    double margin = high > low ? (high - low) / 8 : 1;
    pl_set_title(axes, "first values (dots: left side; line: right side)");
    pl_set_xlim(axes, (double)base - 0.5, (double)(base + rows) - 0.5);
    pl_set_ylim(axes, low - margin, high + margin);
    pl_set_xticks(axes, at, label, rows);
}

/* 40b. Registra il passo induttivo dell'enunciato side[0] = side[1], con
 * caso base `base`, se ha la forma descritta in testa a 40b: per ogni
 * membro quello che diventa per n + 1 (EXPLAIN_TARGET) e i passaggi che lo
 * portano alla forma finale (EXPLAIN_REWRITE), prima il membro di sinistra.
 * Ogni anello si rilegge e si ricontrolla (reread_equal()); uno che non
 * regge è un errore. Se la forma è un'altra, o le espressioni sono troppo
 * lunghe da scrivere, o i due membri non arrivano alla stessa scrittura,
 * non registra nulla: non è un errore, il passo resta nella dimostrazione. */
static void explain_induction_step(const Node *const side[2], long long base) {
    int variable = induction_var, sum = -1;
    for (int s = 0; s < 2; s++) {
        const Node *big = side[s];
        if (big->kind == N_BIGOP && big->b->kind == N_VAR && big->b->name == variable && !node_uses_letter(big->a, variable) &&
            !node_uses_letter(big->c, variable) && !node_has_bigop(big->c) && !node_has_bigop(side[1 - s])) sum = s;
    }
    if (sum < 0) return;
    const Node *big = side[sum], *other = side[1 - sum], *successor = node_affine(1, variable, 1);
    const char *last = big->op ? " \\cdot " : " + ";
    Rat n = rat_atom(atom_var(variable)), next = rat_add(n, rat_int(1), 0);
    const char *text[6];
    Span line[6], canonical;
    size_t start = proof_length;

    /* Il membro con la somma, per n + 1; poi con l'ultimo termine staccato.
     * Un \prod prende come corpo tutti i fattori che lo seguono (capitolo
     * 9): senza parentesi inghiottirebbe quello nuovo. */
    put_side(big, successor);
    text[0] = explain_span(start, &line[0]);
    start = proof_length;
    if (big->op) proof_add("\\left(");
    put_side(big, NULL);
    if (big->op) proof_add("\\right)");
    for (int pass = 1; pass <= 2; pass++) {
        /* L'ultimo termine: il corpo con l'indice che vale n + 1. Al
         * secondo giro, prima, l'altro membro al posto della somma. */
        proof_add("%s", last);
        shown_name = big->name;
        shown_value = successor;
        put_node(big->c, big->op ? 4 : 2);
        shown_value = NULL;
        text[pass] = explain_span(start, &line[pass]);
        start = proof_length;
        if (pass == 1) put_node(other, big->op ? 3 : 1);
    }

    /* I conti: l'altro membro in n, più (o per) l'ultimo termine; e l'altro
     * membro in n + 1. */
    env_count = 0;
    library_depth = 0;
    env_push(big->name, next);
    Rat term = eval(big->c), known = side_value(other, n);
    start = proof_length;
    int written = put_value("", big->op ? rat_mul(known, term) : rat_add(known, term, 0), &canonical);
    text[3] = explain_span(start, &line[3]);
    start = proof_length;
    put_side(other, successor);
    text[4] = explain_span(start, &line[4]);
    start = proof_length;
    written = written && put_value("", side_value(other, next), &canonical);
    text[5] = explain_span(start, &line[5]);
    if (failure || !written || explain_broken || strcmp(text[3], text[5]) != 0) { failure = NULL; return; }

    /* Gli anelli, riletti. */
    if (!reread_equal(line[0], line[1], base) || !reread_equal(line[1], line[2], base) || !reread_equal(line[2], line[3], base) ||
        !reread_equal(line[4], line[5], base)) { explain_wrong = 1; return; }

    /* I passi: prima il membro di sinistra dell'enunciato. */
    for (int s = 0; s < 2; s++) {
        int first = s == sum ? 0 : 4, count = s == sum ? 4 : 2;
        explain_step(EXPLAIN_TARGET, s + 1)->text[0] = text[first];
        for (int i = 1; i < count; i++) {
            ExplainStep *step = explain_step(EXPLAIN_REWRITE, s + 1);
            step->text[0] = text[first + i];
            step->flag = s != sum || i == 3 ? REWRITE_EXPAND : i == 2 ? REWRITE_HYPOTHESIS : big->op ? REWRITE_SPLIT_PRODUCT : REWRITE_SPLIT_SUM;
        }
    }
}

/* 40b. Registra in `explanation` la spiegazione dell'enunciato formula, che
 * il capitolo 13 ha appena dimostrato per induzione con il verdetto
 * *verdict: che cosa afferma, i primi valori dei due membri, il caso base,
 * l'ipotesi, il passo svolto (explain_induction_step()), e con i grafici
 * accesi il grafico dei primi valori. Non cambia il verdetto, e rimette
 * com'era ciò che il conto lascia in giro. Se l'enunciato non è tra quelli
 * che si sanno spiegare la spiegazione resta vuota; se un controllo
 * fallisce resta vuota e unjustified_steps sale. */
void explain_induction(const char *formula, const Verdict *verdict) {
    Statement statement = {NULL, NULL, REL_EQ};
    explanation.steps = 0;
    if (verdict->outcome != PROVED || !verdict->variable || !verdict->proof || strstr(formula, "\\frac{d")) return;

    /* Lo stato da rimettere com'era. */
    Scratch mark = scratch_mark();
    const char *was = failure;
    int memory = work_allocation_failed, stack = stack_exhausted;
    long long base = verdict->base;
    Frac value[EXPLAIN_VALUES][2];
    failure = NULL;
    explain_wrong = explain_broken = 0;
    explain_capture(1);
    explanation.variable = induction_var = verdict->variable;
    explanation.request = EXPLAIN_INDUCTION;
    explanation.equivalence = explanation.comparisons = explanation.columns = explanation.lines = 0;
    if (!parse_statement(formula, &statement) || statement.relation != REL_EQ) explain_broken = 1;
    const Node *const side[2] = {statement.lhs, statement.rhs};
    int rows = 0;

    /* L'enunciato, com'è scritto, e il caso base. */
    if (!explain_broken) {
        ExplainStep *ask = explain_step(EXPLAIN_ASK, 0);
        Span member[2];
        size_t start = proof_length;
        member[0] = put_side(side[0], NULL);
        proof_add(" = ");
        member[1] = put_side(side[1], NULL);
        ask->text[0] = explain_piece(start);
        start = proof_length;
        proof_add("%lld", base);
        ask->text[1] = explain_piece(start);
        if (!explain_broken && !reread_equal(member[0], member[1], base)) explain_wrong = 1;
    }

    /* I primi valori: i due membri in n, scritti e riletti, e uguali. Un
     * valore che non è un numero razionale (un parametro, una radice)
     * ferma la tabella. */
    for (; rows < EXPLAIN_VALUES && !explain_broken && !explain_wrong; rows++) {
        long long n = base + rows;
        const char *text[2][2];
        int known = 1;
        for (int s = 0; s < 2 && known; s++) {
            Num number;
            Span written[2];
            known = rat_number(side_value(side[s], rat_int(n)), &number) && !failure && number.im.num == 0;
            failure = NULL;
            if (!known) break;
            value[rows][s] = number.re;
            size_t start = proof_length;
            put_side(side[s], node_num(n));
            text[s][0] = explain_span(start, &written[0]);
            start = proof_length;
            put_frac(number.re);
            text[s][1] = explain_span(start, &written[1]);
            if (!explain_broken && !reread_equal(written[0], written[1], n)) explain_wrong = 1;
        }
        if (!known) break;
        if (frac_cmp(value[rows][0], value[rows][1]) != 0) explain_wrong = 1;
        ExplainStep *step = explain_step(EXPLAIN_VALUE, 0);
        size_t start = proof_length;
        proof_add("%lld", n);
        step->text[0] = explain_piece(start);
        step->text[1] = text[0][1];
        step->text[2] = text[1][1];

        /* Il caso base è la prima riga, con i membri scritti per esteso. */
        if (rows) continue;
        step = explain_step(EXPLAIN_BASE, 0);
        for (int s = 0; s < 2; s++) {
            step->text[s] = text[s][0];
            step->text[2 + s] = text[s][1];
        }
    }
    if (rows < 2) explain_broken = 1;

    /* L'ipotesi, il passo, la conclusione: count dice se il passo è svolto. */
    if (!explain_wrong && !explain_broken) {
        explain_step(EXPLAIN_HYPOTHESIS, 0)->text[0] = explanation.step[0].text[0];
        int before = explanation.steps;
        explain_induction_step(side, base);
        int worked = explanation.steps > before;
        explain_step(EXPLAIN_ANSWER, 0)->count = worked;
    }
    if (failure || work_allocation_failed != memory || stack_exhausted != stack) explain_broken = 1;
    if (explain_wrong) unjustified_steps++;
    if (explain_wrong || explain_broken) explanation.steps = 0;
    else if (figures_wanted) induction_figure(base, value, rows);
    explain_capture(0);
    syntax_error = NULL;
    failure = was;
    work_allocation_failed = memory;
    stack_exhausted = stack;
    scratch_drop(mark);
}
