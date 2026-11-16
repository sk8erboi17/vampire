/* MODULO engine_statement: dimostrare un enunciato: quale capitolo lo legge, e
 * il verdetto (capitolo 20).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_statement.h, e
 * il resto è static. */
#include "engine_statement.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"
#include "engine_sets.h"
#include "engine_sign_tables.h"
#include "engine_explanation.h"
#include "engine_quantifiers_verdict.h"
#include "engine_sequences.h"
#include "engine_derivatives.h"
#include "engine_logic.h"
#include "engine_limits.h"
#include "engine_integrals.h"
#include "engine_linear_algebra.h"
#include "engine_multivariable.h"
#include "engine_indices.h"

/* =============================================================================
 * 20. DIMOSTRARE UN ENUNCIATO
 * ============================================================================
 *
 * Il punto d'ingresso unico: sceglie il metodo guardando la notazione.
 *
 * Due notazioni vengono guardate subito, dopo il segno di integrale, perché
 * sono del capitolo 28 qualunque cosa le accompagni, tranne che con un
 * insieme di numeri: il numero di elementi di un insieme, |S|
 * (uses_cardinality()), di cui il capitolo 28 legge solo il confronto con un
 * numero scritto (17x), e allora il verdetto deve dire quel motivo; e
 * l'equipotenza, A \sim B (17w, 28q; uses_equipotence()). Poi un enunciato che dichiara una relazione o
 * un'applicazione tra le parti di un insieme, con \mathcal{P}(S)^{2} o
 * \colon \mathcal{P}(S), va allo svolgimento di 17r e da lì al capitolo 15
 * (uses_parts_relations()); uno che scrive un insieme con una regola,
 * \{(x, y) \mid ...\}, parla di elementi (uses_elements()).
 *
 * Le convenzioni, nell'ordine in cui si applicano. Un enunciato che nomina un
 * insieme numerico, con \mathbb, va alle regole sui quantificatori: ogni sua
 * lettera deve essere quantificata su uno di quegli insiemi, quindi non c'è
 * modo di leggerlo in un altro senso. Tra gli altri, quello che parla di
 * elementi (dichiara qualcosa con \colon, quantifica una lettera minuscola,
 * dice x \in X) è un enunciato su insiemi qualsiasi, e va al capitolo 28.
 * Negli altri una lettera maiuscola senza pedice è un insieme: un enunciato
 * che ne contiene una, o che usa un simbolo proprio degli insiemi, va alla
 * decisione per regioni. Ogni altro va
 * all'induzione, dove le maiuscole compaiono solo con un pedice, come F_{k}:
 * a quella del capitolo 13 se è un'uguaglianza, a quella del capitolo 25 se
 * è una disuguaglianza. Prima però, se contiene \implies, è un enunciato su
 * una successione definita per ricorrenza, e va al capitolo 26: negli altri
 * enunciati senza \mathbb un'implicazione non ha posto. E prima ancora, se
 * comincia con il segno di derivata di Leibniz, va al capitolo 27; se
 * comincia con \lim, anche dopo \nexists, è un limite e va al capitolo 29.
 * Prima di tutto, un enunciato che comincia con \int è un integrale, e va al
 * capitolo 30, qualunque cosa contenga dopo. E prima ancora di questo, un
 * enunciato che scrive una matrice per esteso, con \begin{pmatrix} o un
 * ambiente simile, va al capitolo 32 (uses_matrices()): lì una maiuscola è
 * una matrice, non un insieme, e nessun altro capitolo legge quegli ambienti.
 * E prima di quello, un enunciato che scrive l'insieme delle soluzioni di un
 * sistema lineare, \{(x, y) \in \mathbb{R}^{2} \mid ...\}, va al capitolo 33
 * (uses_linear_systems()): nessun altro capitolo legge \mathbb{R} con un
 * esponente dopo le incognite.
 *
 * Guardare solo i simboli non basta, e ha già causato una dimostrazione falsa:
 * S \times T = T \times S non contiene né unioni né inclusioni, veniva letto
 * come prodotto di due numeri, e come tale risultava vero. Per i prodotti
 * cartesiani è falso. Il caso è ora nei test di antiregressione.
 */

/* Ritorna 1 se formula è un enunciato sugli insiemi, secondo la convenzione
 * descritta in testa al capitolo. Usa il lettore di token del parser, e lascia
 * il suo stato da reimpostare. */
static int uses_set_notation(const char *formula) {
    static const char *const commands[] = {"cup", "cap", "setminus", "subseteq", "supseteq", "emptyset",
                                            "varnothing", "mathcal", "triangle", "exists"};
    int found = 0;
    syntax_error = NULL;
    cursor = formula;
    next_token();
    while (token.kind != T_END && !found) {
        if (token.kind == T_LETTER && isupper(token.ch)) {
            /* Una maiuscola è un insieme se non è seguita da un pedice. */
            next_token();
            found = !is_char('_');
            continue;
        }
        for (size_t i = 0; token.kind == T_COMMAND && i < sizeof commands / sizeof *commands; i++)
            if (strcmp(token.name, commands[i]) == 0) found = 1;
        next_token();
    }
    syntax_error = NULL;
    return found;
}

/* Ritorna 1 se formula parla di elementi di insiemi qualsiasi, cioè è un
 * enunciato del linguaggio di 17o: dichiara qualcosa con \colon, oppure un
 * suo quantificatore lega una lettera minuscola, oppure dice di una lettera
 * minuscola, anche con pedice numerico, che appartiene a qualcosa, oppure
 * scrive un insieme con una regola, \{x \mid ...\} o \{(x, y) \mid ...\}
 * (17p). Gli enunciati sugli
 * insiemi del capitolo 14 quantificano solo lettere maiuscole, non
 * dichiarano nulla, non nominano elementi, e tra graffe conoscono solo
 * \emptyset. Usa il lettore di token del parser, e lascia il suo stato da
 * reimpostare. */
static int uses_elements(const char *formula) {
    int found = 0;
    syntax_error = NULL;
    cursor = formula;
    int named = 0;
    for (next_token(); token.kind != T_END && !found; ) {
        int quantifier = is_command("forall") || is_command("exists"), element = token.kind == T_LETTER && islower(token.ch);
        int braces = is_char(ESCAPED + '{'), family = named && is_command("subseteq");

        /* 17v. L'unione di una famiglia di parti, un'appartenenza negata, una
         * lettera contenuta in \mathcal{P}(S) (una famiglia di parti, F
         * \subseteq \mathcal{P}(S)): il capitolo 14 non ne ha, perché per lui
         * una lettera è un insieme di elementi e \mathcal{P}(S) no. named
         * dice se il token appena letto chiude un nome, F o F_{1}. */
        found = is_command("colon") || is_command("bigcup") || is_command("bigcap") || is_command("notin");
        named = token.kind == T_LETTER || is_char('}');
        /* Il nome va superato intero: in c_{12} \in S il token dopo c
         * e il pedice, ma quello dopo il nome e l'appartenenza. */
        if (element) { int index; abstract_name(&index); }
        else next_token();
        if (family && is_command("mathcal")) found = 1;
        if (quantifier && token.kind == T_LETTER && islower(token.ch)) found = 1;
        if (element && (is_command("in") || is_command("notin"))) found = 1;
        if (braces && (token.kind == T_OPEN || (token.kind == T_LETTER && islower(token.ch)))) found = 1;
    }
    syntax_error = NULL;
    return found;
}

/* Ritorna 1 se formula parla del numero di elementi di un insieme, |S|.
 * La legge solo il capitolo 28, e solo confrontata con un numero scritto
 * (17x): |\mathcal{P}(S)| = 2^n chiede di contare per induzione sul numero
 * degli elementi, e "un insieme infinito ha una parte numerabile" l'assioma
 * della scelta. Dove il lettore non arriva il verdetto deve dire questo,
 * invece di riportare il simbolo su cui si è fermato (prove_core()).
 *
 * Una sbarra verticale è un numero di elementi quando la segue ciò che
 * indica un insieme: una graffa \{, \mathcal o \bigcup, e, se letters è 1,
 * una lettera maiuscola senza pedice (la convenzione di
 * uses_set_notation()). Il valore assoluto dei capitoli 9 e 18 ha dentro
 * un'espressione, che non comincia mai con le prime; in un enunciato con
 * \mathbb una maiuscola può essere un numero, e lì chi chiama passa
 * letters = 0. Usa il lettore di token del parser, e lascia il suo stato da
 * reimpostare. */
static int uses_cardinality(const char *formula, int letters) {
    int found = 0;
    syntax_error = NULL;
    cursor = formula;
    for (next_token(); token.kind != T_END && !found; ) {
        int bar = is_char('|') || token.kind == T_ABS_OPEN;
        next_token();
        if (!bar) continue;
        if (is_char(ESCAPED + '{') || is_command("mathcal") || is_command("bigcup") || is_command("bigcap")) found = 1;
        else if (letters && token.kind == T_LETTER && isupper(token.ch)) { next_token(); found = !is_char('_'); }
    }
    syntax_error = NULL;
    return found;
}

/* 17w. Ritorna 1 se formula scrive un'equipotenza, A \sim B. Usa il lettore
 * di token del parser, e lascia il suo stato da reimpostare. */
static int uses_equipotence(const char *formula) {
    int found = 0;
    syntax_error = NULL;
    cursor = formula;
    for (next_token(); token.kind != T_END && !found; next_token()) found = is_command("sim");
    syntax_error = NULL;
    return found;
}

/* Ritorna 1 se formula dichiara una relazione o un'applicazione tra le
 * parti di un insieme (17r): \colon \mathcal{P}(S), oppure \in
 * \mathcal{P}(S)^{2} o \in \mathcal{P}(S) \times \mathcal{P}(S), che si
 * scrivono solo nella regola di una relazione tra parti. \forall X \in
 * \mathcal{P}(S), senza il quadrato, è del capitolo 14 e non conta. Usa il
 * lettore di token del parser, e lascia il suo stato da reimpostare. */
static int uses_parts_relations(const char *formula) {
    int found = 0;
    syntax_error = NULL;
    cursor = formula;
    for (next_token(); token.kind != T_END && !found; ) {
        int colon = is_command("colon"), in = is_command("in");
        next_token();
        if (!is_command("mathcal") || (!colon && !in)) continue;
        if (colon) { found = 1; continue; }

        /* \in \mathcal{P}(L): dopo \mathcal, sette token, { P } ( L ); poi
         * il quadrato, o \times e un altro \mathcal. */
        for (int skip = 0; skip < 7 && token.kind != T_END; skip++) next_token();
        int square = is_char('^'), times = is_command("times");
        next_token();
        found = square || (times && is_command("mathcal"));
    }
    syntax_error = NULL;
    return found;
}

/* Ritorna 1 se in text c'è un segno di derivata di Leibniz, in un punto
 * qualsiasi (starts_with_derivative()). */
static int has_derivative_sign(const char *text) {
    for (const char *p = strchr(text, '\\'); p; p = strchr(p + 1, '\\'))
        if (starts_with_derivative(p)) return 1;
    return 0;
}

/* DENTRO VAMPIRE: GLI ENUNCIATI SUI NUMERI CHE IL MOTORE NON DECIDE
 *
 * A che cosa serve. "Per ogni a, b, c interi, se (ab - 2)(a - b) = 0 e
 * (bc - 2)(b - c) = 0 allora (ac - 2)(a - c) = 0." Il motore lo legge, e le
 * sue regole sui quantificatori (capitolo 18) non bastano né a dimostrarlo
 * né a smentirlo. Vampire ha le teorie dell'aritmetica degli interi, dei
 * razionali e dei reali, e questo lo dimostra. Perché ci arrivi, l'enunciato
 * va consegnato in una forma che dica esattamente la stessa cosa.
 *
 * Che cosa si consegna. Solo ciò che si traduce senza interpretare:
 *
 *   - quantificatori su insiemi di numeri tutti dello stesso genere: tutti
 *     di interi (\mathbb{N}, \mathbb{N}_{0}, \mathbb{Z}), o tutti di
 *     razionali (\mathbb{Q}, \mathbb{Q}^{+}), o tutti di reali, con il loro
 *     estremo inferiore e i punti tolti. Con generi diversi insieme la
 *     traduzione dovrebbe scegliere come passare dagli uni agli altri, e non
 *     si consegna;
 *   - i connettivi, i confronti =, \neq, <, \le, l'appartenenza di
 *     un'espressione a un insieme dello stesso genere (che è allora il suo
 *     estremo e i suoi punti tolti) e, tra interi, la divisibilità;
 *   - espressioni fatte di numeri interi scritti, lettere legate, somma,
 *     differenza, opposto, prodotto, potenza con esponente intero scritto
 *     da 1 a 16, e, tra razionali e tra reali, divisione per un intero
 *     scritto diverso da zero.
 *
 * Tutto il resto resta al motore: applicazioni dichiarate, parametri,
 * coppie, numeri complessi, segni di derivata, funzioni, radici, esponenti
 * che sono lettere, divisioni per un'espressione (che chiederebbero di dire
 * dove il divisore è zero), richieste di soluzioni.
 *
 * La notazione. Una riga "numbers int", "numbers rat" o "numbers real", poi
 * l'enunciato a parentesi:
 *
 *     (forall x SET C)  (exists x SET C)     x è (var N), N la lettera
 *     SET = (set [ge L | gt L] [except P/Q]...)
 *     (and C C) (or C C) (implies C C) (iff C C) (not C)
 *     (= E E) (neq E E) (less E E) (lesseq E E)
 *     (in E SET)  (divides E E)              "il primo divide il secondo"
 *     E = N | (var N) | (add E E) | (sub E E) | (neg E) | (mul E E)
 *       | (pow E K) | (div E N)
 *
 * La divisibilità è quella di 17n: u divide v se v è u per un intero, quindi
 * zero divide solo zero. Chi riceve la traduce così.
 *
 * Che cosa vale ciò che torna. Una dimostrazione di Vampire su questo testo
 * non passa da checker.c, che non ha un linguaggio per l'aritmetica con i
 * quantificatori: il verdetto di chi ospita il motore deve dire "prova
 * trovata, non verificata". Il motore, da parte sua, non dichiara nulla.
 */

/* Le lettere legate nel punto dell'enunciato che numbers_formula() sta
 * scrivendo, dalla più esterna: un'espressione può usare solo queste. */
static _Thread_local int numbers_bound[64], numbers_bound_count;

/* Il genere dei numeri dell'enunciato consegnato: 0 non ancora fissato, poi
 * 1 interi, 2 razionali, 3 reali. Lo fissa il primo insieme incontrato, e
 * tutti gli altri devono avere lo stesso. */
static _Thread_local int numbers_base;

/* Scrive l'insieme di numeri set. Ritorna 0 se non è del genere degli altri
 * insiemi dell'enunciato, o è \mathbb{C}. */
static int numbers_set(const NumberSet *set) {
    int base = set->complex ? 0 : set->integers ? 1 : set->reals ? 3 : 2;
    if (!base || (numbers_base && numbers_base != base)) return 0;
    numbers_base = base;
    cert_add("(set");
    if (set->bounded) cert_add(" %s %lld", set->strict ? "gt" : "ge", set->low);
    for (int i = 0; i < set->holes; i++) cert_add(" except %lld/%lld", set->hole[i].num, set->hole[i].den);
    cert_add(")");
    return 1;
}

/* Scrive l'espressione n. Ritorna 0 se ha qualcosa che non si consegna
 * (vedi sopra): una lettera non legata, una funzione, un esponente che non
 * è un intero scritto da 1 a 16, una divisione che non è per un intero
 * scritto diverso da zero, o una divisione tra interi. */
static int numbers_term(const Node *n) {
    static const char *const word[] = {[N_ADD] = "add", [N_SUB] = "sub", [N_MUL] = "mul"};
    if (!n) return 0;
    switch (n->kind) {
    case N_NUM:
        if (n->value < 0) return 0;
        cert_add("%lld", n->value);
        return 1;
    case N_VAR:
        for (int i = 0; i < numbers_bound_count; i++)
            if (numbers_bound[i] == n->name) { cert_add("(var %d)", n->name); return 1; }
        return 0;
    case N_NEG:
        cert_add("(neg ");
        if (!numbers_term(n->a)) return 0;
        cert_add(")");
        return 1;
    case N_ADD: case N_SUB: case N_MUL:
        cert_add("(%s ", word[n->kind]);
        if (!numbers_term(n->a)) return 0;
        cert_add(" ");
        if (!numbers_term(n->b)) return 0;
        cert_add(")");
        return 1;
    case N_POW:
        if (!n->b || n->b->kind != N_NUM || n->b->value < 1 || n->b->value > 16) return 0;
        cert_add("(pow ");
        if (!numbers_term(n->a)) return 0;
        cert_add(" %lld)", n->b->value);
        return 1;
    case N_DIV:
        /* Tra interi il quoziente non è un intero: sarebbe un altro genere. */
        if (numbers_base == 1 || !n->b || n->b->kind != N_NUM || n->b->value <= 0) return 0;
        cert_add("(div ");
        if (!numbers_term(n->a)) return 0;
        cert_add(" %lld)", n->b->value);
        return 1;
    default:
        return 0;
    }
}

/* Scrive la condizione f. Ritorna 0 se ha qualcosa che non si consegna. */
static int numbers_formula(const Formula *f) {
    static const char *const word[] = {[F_EQUAL] = "=", [F_DISTINCT] = "neq", [F_LESS] = "less", [F_LESS_EQ] = "lesseq",
                                       [F_AND] = "and", [F_OR] = "or", [F_IMPLIES] = "implies", [F_IFF] = "iff"};
    if (!f) return 0;
    switch (f->kind) {
    case F_EQUAL: case F_DISTINCT: case F_LESS: case F_LESS_EQ:
        cert_add("(%s ", word[f->kind]);
        if (!numbers_term(f->left)) return 0;
        cert_add(" ");
        if (!numbers_term(f->right)) return 0;
        cert_add(")");
        return 1;
    case F_AND: case F_OR: case F_IMPLIES: case F_IFF:
        cert_add("(%s ", word[f->kind]);
        if (!numbers_formula(f->a)) return 0;
        cert_add(" ");
        if (!numbers_formula(f->b)) return 0;
        cert_add(")");
        return 1;
    case F_NOT:
        cert_add("(not ");
        if (!numbers_formula(f->a)) return 0;
        cert_add(")");
        return 1;
    case F_FORALL: case F_EXISTS:
        /* Una coppia (17t-2) o un quantificatore sul resto non si traducono. */
        if (f->pair || f->complex || numbers_bound_count == (int)(sizeof numbers_bound / sizeof *numbers_bound)) return 0;
        cert_add("(%s (var %d) ", f->kind == F_FORALL ? "forall" : "exists", f->variable);
        if (!numbers_set(&f->numbers)) return 0;
        cert_add(" ");
        numbers_bound[numbers_bound_count++] = f->variable;
        int written = numbers_formula(f->a);
        numbers_bound_count--;
        if (!written) return 0;
        cert_add(")");
        return 1;
    case F_IN:
        /* \notin è la negazione (swapped). */
        if (f->swapped) cert_add("(not ");
        cert_add("(in ");
        if (!numbers_term(f->left)) return 0;
        cert_add(" ");
        if (!numbers_set(&f->numbers)) return 0;
        cert_add(f->swapped ? "))" : ")");
        return 1;
    case F_DIVIDES:
        /* Solo tra interi: tra razionali "divide" chiede un quoziente
         * intero, che è di nuovo un altro genere. \nmid è la negazione. */
        if (numbers_base != 1) return 0;
        if (f->swapped) cert_add("(not ");
        cert_add("(divides ");
        if (!numbers_term(f->left)) return 0;
        cert_add(" ");
        if (!numbers_term(f->right)) return 0;
        cert_add(f->swapped ? "))" : ")");
        return 1;
    default:
        return 0;
    }
}

/* Dentro Vampire (LOGIC_NUMBERS). Legge l'enunciato con quantificatori sui
 * numeri scritto in formula e, se sta nel frammento descritto sopra, lo
 * consegna: NOT_PROVED con reason == LOGIC_HANDED_OVER e il testo in
 * detail. Altrimenti NOT_PROVED con il motivo, e nulla da consegnare. Non
 * decide nulla.
 *
 * Svuota l'arena e le tabelle dell'enunciato, come decide_quantified(), di
 * cui ripete la lettura: i risultati di chiamate precedenti non sono più
 * validi. */
static Verdict numbers_handed_over(const char *formula) {
    Verdict verdict = {NOT_PROVED, 0, 0, 0, "l'enunciato non sta nel frammento che si consegna alle teorie aritmetiche di Vampire",
                       NULL, NULL, NULL, NULL, NULL};

    /* La lettura, come in decide_quantified(). */
    proof_reset();
    arena_used = arena_keep;
    atom_count = base_poly_count = atan_count = 0;
    failure = NULL;
    env_count = 0;
    map_count = statement_parameter_count = 0;
    syntax_error = NULL;
    cursor = formula;
    next_token();
    Formula *thesis = logic_statement();
    if (token.kind != T_END) syntax("testo inatteso dopo l'enunciato");
    derivative_signs = 0;
    if (!syntax_error) formula_derivatives_expanded(thesis);
    if (!syntax_error && !failure && !map_count && !pair_set_count && !statement_parameter_count) {
        quantifier_depth = 0;
        formula_check(thesis);
        scope_count = 0;
    }
    int readable = !syntax_error && !failure && !map_count && !pair_set_count && !statement_parameter_count && !derivative_signs;

    /* La scrittura. Il genere dei numeri si conosce solo alla fine, e va in
     * testa: prima si scrive l'enunciato dopo un'intestazione di lunghezza
     * fissa, poi la si riempie. */
    if (readable) {
        static const char *const head[] = {NULL, "numbers int \n", "numbers rat \n", "numbers real\n"};
        certificate_length = 0;
        certificate_broken = 0;
        cert_add("%s", head[3]);
        numbers_base = numbers_bound_count = 0;
        if (numbers_formula(thesis) && numbers_base && !certificate_broken) {
            cert_add("\n");
            if (!certificate_broken) {
                memcpy(certificate_text, head[numbers_base], strlen(head[numbers_base]));
                verdict.reason = LOGIC_HANDED_OVER;
                verdict.detail = certificate_text;
            }
        }
    }

    /* Come prove_quantified(): ciò che l'enunciato ha dichiarato non deve
     * restare visibile al lettore delle espressioni. */
    map_count = statement_parameter_count = 0;
    return verdict;
}

/* Prova a dimostrare l'enunciato scritto in formula.
 *
 * variable, has_base e base riguardano le dimostrazioni per induzione (vedi
 * prove_by_induction()) e sono ignorati per gli altri enunciati.
 *
 * I risultati di una chiamata precedente, comprese le stringhe del suo
 * verdetto, non sono più validi dopo questa. */
static Verdict prove_core(const char *formula, int variable, int has_base, long long base) {
    /* Il grafico dell'enunciato precedente non vale più, e nemmeno la sua
     * spiegazione (capitolo 40). */
    if (figure) { pl_close(figure); figure = NULL; }
    explanation.steps = 0;

    /* Un enunciato lungo lo legge solo il linguaggio degli insiemi
     * qualsiasi (capitolo 28), che cresce con il problema e sorveglia la
     * pila (capitolo 2). Gli altri linguaggi contano su MAX_FORMULA, nei
     * loro depositi e nella profondità dei loro alberi: lo rifiutano, come
     * facevano quando era il lettore degli \item a fermarsi lì. Senza
     * questo rifiuto 6000 radici una dentro l'altra fermavano il programma. */
    const Verdict too_long = {UNSUPPORTED, variable, 0, 0, "enunciato troppo lungo", NULL, NULL, NULL, NULL, NULL};
    stack_guard = strlen(formula) >= MAX_FORMULA;

    /* Dentro Vampire (LOGIC_NUMBERS): l'enunciato non si decide, si
     * consegna, se è di quelli che più sotto andrebbero com'è scritto a
     * prove_quantified() (vedi numbers_handed_over()). Per tutti gli altri
     * la risposta è subito "niente da consegnare": i rami qui sotto li
     * deciderebbero una seconda volta, e non è questo che è stato chiesto.
     * Warning: la condizione ripete, negati, i rami che in questa funzione
     * precedono quello di \mathbb; se ne nasce uno nuovo va aggiunto qui. */
    if (logic_task == LOGIC_NUMBERS) {
        int as_written = !stack_guard && strstr(formula, "\\mathbb") && !uses_partial_notation(formula) && !uses_index_notation(formula) &&
                         !uses_linear_systems(formula) && !uses_matrices(formula) && !starts_with_integral(formula) &&
                         !uses_cardinality(formula, 0) && !uses_equipotence(formula);
        if (as_written) return numbers_handed_over(formula);
        return (Verdict){NOT_PROVED, variable, 0, 0, "non è un enunciato con quantificatori sui numeri", NULL, NULL, NULL, NULL, NULL};
    }

    /* L'insieme delle soluzioni di un sistema lineare, \{(x, y) \in
     * \mathbb{R}^{2} \mid ...\}: un enunciato del capitolo 33, anche quando
     * scrive delle matrici. Come per le matrici qui sotto, non se lo
     * prende alle funzioni di più variabili, e non ha lo svolgimento del
     * capitolo 40. */
    if (uses_linear_systems(formula) && !uses_partial_notation(formula)) {
        if (stack_guard) return too_long;
        Verdict verdict = prove_linear(formula);
        explanation.steps = 0;
        return verdict;
    }

    /* Una matrice scritta per esteso: un enunciato del capitolo 32, prima
     * di ogni altra lettura. Tranne quando l'enunciato è sulle funzioni di
     * più variabili (capitolo 35): lì una tabella è il secondo membro di
     * un'hessiana, e la legge quel capitolo, più sotto. Senza questa
     * eccezione 39 enunciati dei test di Analisi 2 finivano qui, e
     * risultavano non supportati.
     *
     * Lo svolgimento (capitolo 40) non vale per queste voci. Con una
     * lettera negli elementi il capitolo 32 consegna alla tabella dei segni
     * l'enunciato che resta dopo aver sviluppato i determinanti, e lo
     * svolgimento spiegherebbe quello, "h - 9 = 0", come se fosse ciò che è
     * stato scritto: finché non sa mostrare anche lo sviluppo, il documento
     * di queste voci è quello senza svolgimento.
     *
     * Un'altra eccezione: un'identità con gli indici (capitolo 38) che tra
     * le ipotesi dà un tensore con una tabella. La legge quel capitolo. */
    if (uses_matrices(formula) && !uses_partial_notation(formula) && !uses_index_notation(formula)) {
        if (stack_guard) return too_long;
        Verdict verdict = prove_matrix(formula);
        if (verdict.outcome == UNSUPPORTED && verdict.reason == LETTER_CASES) verdict = prove_parameter(formula);
        explanation.steps = 0;
        return verdict;
    }

    /* \int in testa: un integrale (capitolo 30), qualunque cosa segua. */
    if (starts_with_integral(formula)) return stack_guard ? too_long : prove_integral(formula);

    /* Il numero di elementi di un insieme e l'equipotenza vanno al capitolo
     * 28, tra insiemi qualsiasi (17x; 17w, 28q); tra insiemi di numeri no.
     * Del primo il capitolo 28 legge solo il confronto con un numero
     * scritto, |S| = 3: se non ha letto l'enunciato e si è fermato prima
     * di incontrarne uno, il motivo è quello (count_reason), e non il
     * simbolo su cui il lettore si è fermato. */
    int numbers = strstr(formula, "\\mathbb") != NULL, counts = uses_cardinality(formula, !numbers);
    if (counts && numbers) return (Verdict){UNSUPPORTED, variable, 0, 0, count_reason, NULL, NULL, NULL, NULL, NULL};
    if (counts || uses_equipotence(formula)) {
        if (numbers)
            return (Verdict){UNSUPPORTED, variable, 0, 0, "l'equipotenza è trattata solo tra insiemi qualsiasi, non con un insieme di numeri", NULL, NULL, NULL, NULL, NULL};
        /* Un esponente che il lettore non sa leggere, S^{T \cup V}, è il
         * motivo vero anche quando il lettore si ferma prima. */
        int bad_exponent = equipotence_bad_exponent(formula);
        Verdict verdict = prove_abstract(formula);
        if (verdict.outcome == UNSUPPORTED && bad_exponent) verdict.reason = equipotence_exponent_reason;
        else if (verdict.outcome == UNSUPPORTED && counts && !count_met) verdict.reason = count_reason;
        return verdict;
    }
    if (strstr(formula, "\\mathbb")) return stack_guard ? too_long : prove_quantified(formula);

    /* Un'identità con gli indici del calcolo tensoriale (capitoli 37 e 38):
     * la riconosce una delta di Kronecker o un simbolo di Levi-Civita con i
     * suoi indici, che nessun altro linguaggio legge (uses_index_notation()). */
    if (uses_index_notation(formula)) return stack_guard ? too_long : prove_indices(formula);

    /* Un enunciato lungo, da qui in poi, è del capitolo 28 o di nessuno.
     * Uno sulle relazioni tra parti che il capitolo 28 non legge poteva
     * essere del capitolo 15 (17r), che gli enunciati lunghi non li legge:
     * il motivo dice tutte e due le cose, perché l'errore del capitolo 28 da
     * solo è fuori posto per un enunciato di 17r, e "troppo lungo" da solo
     * nasconde un errore di scrittura vero. */
    if (stack_guard) {
        static _Thread_local char both[512];
        int parts = uses_parts_relations(formula);
        if (!parts && !uses_elements(formula)) return too_long;
        Verdict verdict = prove_abstract(formula);
        if (parts && verdict.outcome == UNSUPPORTED) {
            snprintf(both, sizeof both, "enunciato troppo lungo per le relazioni tra parti del capitolo 15; come enunciato su insiemi qualsiasi: %s", verdict.reason);
            verdict.reason = both;
        }
        return verdict;
    }

    /* Le funzioni di più variabili (capitolo 35): \partial, \nabla, o una
     * funzione dichiarata e poi \implies. Nessun altro metodo le legge. */
    if (uses_partial_notation(formula)) return prove_partial(formula);

    /* Il segno di derivata in testa: l'enunciato è del capitolo 27, anche
     * quando il capitolo 27 non lo sa leggere. Non prosegue come algebra,
     * perché come algebra \frac{d}{dx} sarebbe la frazione 1/x (vedi
     * starts_with_derivative()); il motivo detto è quello del lettore. */
    if (starts_with_derivative(formula)) {
        Verdict verdict = prove_derivative(formula, variable, has_base, base);
        if (verdict.reason == NOT_A_DERIVATIVE && syntax_error) verdict.reason = syntax_error;
        return verdict;
    }
    /* \lim in testa, anche dopo \nexists: un enunciato sui limiti, del
     * capitolo 29. */
    if (starts_with_limit(formula)) return prove_limit(formula);

    /* Un segno di derivata dentro un'espressione lo espandono (27j) solo
     * gli enunciati con quantificatori, sui numeri reali, e quelli del
     * capitolo 13 e del 25. Negli altri resta un segno che nessuno calcola,
     * e non va letto come altro. */
    if (has_derivative_sign(formula) && (uses_elements(formula) || uses_set_notation(formula) || strstr(formula, "\\implies")))
        return (Verdict){UNSUPPORTED, variable, 0, 0, "il segno di derivata non ha senso in un enunciato su insiemi o su una successione definita per ricorrenza", NULL, NULL, NULL, NULL, NULL};
    /* Una relazione tra parti che il capitolo 15 non sa decidere (troppi
     * insiemi, o una scrittura che 17r non legge) può ancora essere un
     * enunciato del capitolo 28, con \mathcal{P}(S) come insieme di oggetti
     * (17v): se lì non si legge nemmeno, il motivo resta quello di 17r. */
    if (uses_parts_relations(formula)) {
        Verdict verdict = prove_parts(formula);
        if (verdict.outcome != UNSUPPORTED) return verdict;
        Verdict objects = prove_abstract(formula);
        return objects.outcome != UNSUPPORTED ? objects : prove_parts(formula);
    }
    if (uses_elements(formula)) return prove_abstract(formula);
    if (uses_set_notation(formula)) return prove_sets(formula);
    if (strstr(formula, "\\implies")) return prove_sequence(formula, variable, has_base, base);

    /* Un'uguaglianza al capitolo 13; ciò che quello rifiuta perché non è
     * un'uguaglianza, al capitolo 25. */
    Verdict verdict = prove_by_induction(formula, variable, has_base, base);
    if (verdict.reason == NOT_AN_EQUALITY) return prove_inequality(formula, variable, has_base, base);

    /* 40b. La spiegazione di un'induzione riuscita, a verdetto dato: non lo
     * cambia. */
    if (explanations_wanted) explain_induction(formula, &verdict);
    return verdict;
}

/* Scrive su out il verdetto in una riga, senza a capo. */
void verdict_print(FILE *out, const Verdict *verdict) {
    switch (verdict->outcome) {
    case PROVED:
        if (verdict->variable) fprintf(out, "DIMOSTRATO per induzione su %c >= %lld", verdict->variable, verdict->base);
        else fprintf(out, "DIMOSTRATO %s", verdict->method);
        if (verdict->note) fprintf(out, " (%s)", verdict->note);

        /* Il certificato: c'è, oppure manca, e se si sa perché lo si dice. */
        if (!verdict->certificate) {
            fprintf(out, verdict->reason ? "; senza certificato (%s)" : "; senza certificato", verdict->reason);
            break;
        }

        /* Che cosa copre. Per un enunciato sugli insiemi tutto: il
         * verificatore lo ha deciso da capo. Per un'induzione l'uguaglianza
         * dove i due membri sono definiti, e con la voce "defined" anche il
         * fatto che lo siano per ogni n, nel punto che il certificato indica
         * se ci sono parametri. */
        const char *point = strstr(verdict->certificate, "\ndefined");
        if (!verdict->variable) fprintf(out, "; certificato verificato");
        else if (!point) fprintf(out, "; certificato verificato: uguali dove sono definiti");
        else if (point[8] == '\n') fprintf(out, "; certificato verificato: definiti e uguali per ogni %c", verdict->variable);
        else fprintf(out, "; certificato verificato: uguali dove sono definiti, e definiti per ogni %c con i parametri del certificato", verdict->variable);
        if (strstr(verdict->certificate, "\ngeneric ")) fprintf(out, ", con un'ipotesi in più sui parametri");
        break;
    case REFUTED:
        if (verdict->variable) fprintf(out, "FALSO: non vale per %c = %lld", verdict->variable, verdict->witness);
        else if (verdict->detail) fprintf(out, "FALSO: controesempio %s", verdict->detail);
        else fprintf(out, "FALSO: è dimostrata la sua negazione");
        if (verdict->note) fprintf(out, " (%s)", verdict->note);

        /* Il controesempio di un enunciato su insiemi qualsiasi è anche un
         * certificato (28f), che il verificatore ha ricalcolato; quello
         * della tabella dei segni lo è la tabella (18p-15), che può anche
         * mancare, e allora si dice perché. */
        if (verdict->certificate) fprintf(out, "; certificato verificato");
        else if (verdict->reason) fprintf(out, "; senza certificato (%s)", verdict->reason);
        break;
    case NOT_PROVED:
        fprintf(out, "NON DIMOSTRATO: %s", verdict->reason);
        break;
    case UNSUPPORTED:
        fprintf(out, "NON SUPPORTATO: %s", verdict->reason);
        break;
    case SOLVED:
        /* Il certificato prima dei due punti: dopo vengono le soluzioni, e
         * chi le rilegge (tools/fuzz/) le cerca subito dopo il primo ": ". */
        fprintf(out, "RISOLTO %s", verdict->method);
        if (verdict->certificate) fprintf(out, ", certificato verificato");
        else if (verdict->reason) fprintf(out, ", senza certificato (%s)", verdict->reason);
        fprintf(out, ": %s", verdict->detail);
        if (verdict->note) fprintf(out, " (%s)", verdict->note);
        break;
    }
}

/* Punto d'ingresso protetto: una pila o un vettore cresciuti solo in parte
 * rendono inutilizzabile tutto il tentativo, anche se una strada interna
 * ha cancellato failure per provarne un'altra. Ogni chiamata riparte dai
 * contatori inizializzati dai metodi; le capacita allocate si riusano. */
Verdict prove(const char *formula, int variable, int has_base, long long base) {
    work_allocation_failed = stack_exhausted = 0;

    /* Anche il conto delle catene riparte da qui, e non dal lettore: i
     * primi token dell'enunciato passano per la guardia prima di lui, e il
     * conto dell'enunciato precedente lo faceva rifiutare. */
    stack_chain_levels = 0;
    Verdict verdict = prove_core(formula, variable, has_base, base);
    stack_guard = 0;

    /* La pila finita (capitolo 2) viene dopo la memoria: è la causa più
     * precisa, e i lettori fermati a metà possono aver detto altro. */
    if (work_allocation_failed || stack_exhausted) {
        verdict.outcome = NOT_PROVED;
        verdict.reason = stack_exhausted ? STACK_EXHAUSTED : OUT_OF_MEMORY;
        verdict.proof = verdict.certificate = verdict.detail = NULL;
    }
    return verdict;
}

/* Dimostra l'enunciato contenuto nel testo [item, end) di un \item. */
Verdict prove_item(const char *item, const char *end) {
    Item statement;
    const char *problem = read_item(item, end, &statement);
    if (problem) return (Verdict){problem==OUT_OF_MEMORY?NOT_PROVED:UNSUPPORTED, 'n', 0, 0, problem, NULL, NULL, NULL, NULL, NULL};
    Verdict verdict = prove(statement.formula, statement.variable, statement.has_base, statement.base);

    /* Una condizione scritta dopo la formula restringe i casi di cui parla
     * l'enunciato: "per ogni n pari", "con 0 < x < 1". Se il programma non
     * l'ha letta, una dimostrazione resta valida, perché copre anche quei
     * casi; un controesempio invece potrebbe essere proprio uno dei casi
     * esclusi, quindi non basta a dire FALSO. Senza questa cautela la somma
     * dei (-1)^k "per ogni n pari" risultava falsa per n = 1. */
    if (statement.conditional && verdict.outcome == REFUTED) {
        const char *reason = "in generale non vale, ma dopo la formula c'è una condizione che il programma non sa leggere";
        return (Verdict){NOT_PROVED, verdict.variable, 0, 0, reason, NULL, NULL, NULL, NULL, NULL};
    }

    /* Un inciso letto come commento non ferma un FALSO, ma chi legge il
     * verdetto deve sapere che c'era e che non è stato considerato. */
    if (statement.remark && verdict.outcome == REFUTED) verdict.note = "ignorato un commento tra parentesi dopo la formula";
    return verdict;
}
