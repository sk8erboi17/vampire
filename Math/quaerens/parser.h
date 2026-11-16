/* INTERFACCIA DI parser.c: la lettura del LaTeX: gli alberi delle espressioni,
 * degli enunciati sugli insiemi, di quelli con quantificatori, delle matrici e
 * degli indici, i lettori che li costruiscono, gli \item di un file (capitoli
 * 8, 9, 14, 17, 21, 31, 34, 37 e 39).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * parser.c. Ciò che il modulo usa solo per sé non è qui: là è static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_PARSER_H
#define QUAERENS_PARSER_H

#include "engine_foundations.h"

/* Tipi di nodo. Tra parentesi i figli usati.
 *
 * Warning: se aggiungi un tipo, aggiungi il ramo che lo costruisce nel parser
 * (capitolo 9) e il suo case in eval() (capitolo 11); se può comparire in un
 * enunciato con quantificatori, anche in term_check() (capitolo 17). */
typedef enum {
    N_NUM,    /* intero letterale: value */
    N_VAR,    /* variabile: name */
    N_SEQ,    /* lettera con pedice, come F_{k}: name, a = pedice */
    N_NEG,    /* -a */
    N_ADD,    /* a + b */
    N_SUB,    /* a - b */
    N_MUL,    /* a * b */
    N_DIV,    /* a / b */
    N_POW,    /* a ^ b */
    N_BIGOP,  /* somma o prodotto: name = indice, a = estremo inferiore,
                 b = estremo superiore, c = corpo, op = 1 se è un prodotto */
    N_CALL,   /* funzione: op = quale (Function), a = argomento, b = secondo
                 argomento se c'è */
    N_APPLY,  /* applicazione dichiarata dall'enunciato, come f(x): name = la
                 lettera f, a = argomento */
    N_DERIV   /* segno di derivata di Leibniz dentro un'espressione (9d):
                 name = la variabile x, value = l'ordine (un numero da 1 in
                 su), a = la funzione da derivare. Lo crea solo il lettore, e
                 il motore lo sostituisce con la derivata prima di ogni conto
                 (27j): eval() e le altre letture dell'albero non lo trattano */
} NodeKind;

/* Le funzioni che il parser riconosce. Il secondo argomento, quando esiste, è
 * indicato tra parentesi.
 *
 * Warning: se aggiungi una funzione, aggiungi il suo nome in function_names[]
 * (capitolo 9), se è un comando LaTeX, e il suo case in eval_call(). */
typedef enum {
    FN_FACT,    /* a! */
    FN_BINOM,   /* coefficiente binomiale "a su b" */
    FN_SIN, FN_COS, FN_TAN, FN_COT,
    FN_ARCTAN,
    FN_LN,
    FN_LOG,     /* logaritmo di a in base b */
    FN_ROOT,    /* radice di a di indice b */
    FN_ABS,     /* valore assoluto */
    FN_ARCSIN, FN_ARCCOS,  /* le inverse di seno e coseno, a valori in
                              [-pi/2, pi/2] e in [0, pi] */
    FN_ARCCOT   /* l'inversa della cotangente, a valori in (0, pi) */
} Function;

/* Un nodo dell'albero: una sotto-espressione dell'enunciato. I figli non usati
 * dal tipo sono NULL. I nodi vivono nell'arena. */
struct Node {
    NodeKind kind;
    long long value;  /* N_NUM */
    int name;         /* N_VAR, N_SEQ, N_BIGOP: una lettera, o VAR_PI */
    int op;           /* N_BIGOP, N_CALL */
    Node *a, *b, *c;
};

int node_equal(const Node *a, const Node *b);
int bigop_same(const Node *a, const Node *b);

/* Un insieme di numeri razionali tra quelli che un enunciato può nominare:
 * \mathbb{N}, \mathbb{N}_{0}, \mathbb{Z}, \mathbb{Q}, \mathbb{Q}^{+}, privati
 * eventualmente di qualche punto con \setminus. È l'insieme su cui varia la
 * variabile di un quantificatore, oppure il dominio o il codominio di
 * un'applicazione. Le operazioni sono nel capitolo 17.
 *
 * Invariante: i punti tolti sono distinti e appartengono tutti all'insieme di
 * partenza, così due insiemi uguali hanno gli stessi punti in `hole`. */
typedef struct {
    int integers;             /* 1: solo numeri interi; 0: tutti i razionali */
    int reals;                /* 1: tutti i numeri reali, non solo i razionali */
    int complex;              /* 1: i numeri complessi, che il lettore legge come coppie di
                                 reali (17s): resta 1 solo finché pairs_second() non li divide */
    int bounded;              /* 1: c'è un estremo inferiore, `low` */
    long long low;            /* l'estremo inferiore, se bounded */
    int strict;               /* 1: low è escluso (x > low); 0: è compreso */
    int holes;                /* punti tolti, validi in `hole` */
    Frac hole[MAX_HOLES];
    const char *start, *end;  /* com'è scritto nell'enunciato: [start, end) */
} NumberSet;

/* Un caso di un'applicazione definita per casi (17s): "se vale when, allora
 * f(x) = value". when è una condizione sulla sola variabile x della regola
 * (e sui parametri dell'enunciato), fatta di confronti, divisibilità e
 * appartenenze legati da connettivi; value è un'espressione razionale. Gli
 * alberi stanno nell'arena. Il tipo delle condizioni, Formula, è definito
 * nel capitolo 17: qui basta il nome della struttura. */
typedef struct {
    const struct Formula *when;  /* la condizione del caso */
    Node *value;                 /* il valore di f(x) quando la condizione vale */
} MapCase;

/* Un'applicazione dichiarata dall'enunciato con "f \colon A \to B". La regola
 * che la definisce, "f(x) = espressione", arriva dopo, da un'altra ipotesi:
 * finché manca, body è NULL, cases è 0 e parameter non ha significato.
 *
 * Una regola può essere data per casi (17s): allora i casi stanno in
 * piece[], e il valore di f(x) è quello del caso la cui condizione vale.
 * body resta NULL, salvo quando i casi vengono da una regola sola con dei
 * valori assoluti: allora body è quella regola com'è scritta, e serve solo a
 * ricontrollare sui numeri che i casi dicano lo stesso.
 *
 * Un'operazione binaria, dichiarata con "\ast \colon A \times B \to C", è
 * un'applicazione con due argomenti: la sua regola è "x \ast y = espressione"
 * (vedi 9g). second e parameter2 servono solo a lei. */
typedef struct {
    int name;                    /* la lettera f, oppure il nome interno di un
                                    simbolo di operazione (operation_name()) */
    NumberSet domain, codomain;  /* A e B; per un'operazione A e C */
    int parameter;               /* la variabile x della regola */
    Node *body;                  /* il valore di f(x), nell'arena; NULL se manca */
    int binary;                  /* 1 se è un'operazione binaria */
    NumberSet second;            /* operazione: B, l'insieme del secondo argomento */
    int parameter2;              /* operazione: la variabile y della regola */
    int cases;                   /* definizione per casi: casi validi in piece[]; 0 se non lo è */
    MapCase piece[MAX_MAP_CASES];
    int partner;                 /* valori in coppie (17s): il nome dell'applicazione che dà la
                                    seconda componente; questa dà la prima. 0 se i valori sono numeri */
    int component;               /* 2 se è la seconda componente di un'applicazione a valori in
                                    coppie, nascosta dentro di lei; altrimenti 0 */
    int iterates;                /* le iterate (17s): il bit 1 se le ipotesi dicono f^{c} = f, il
                                    bit 2 se dicono f^{n+1} = f \circ f^{n} per n da step_from in su */
    long long iterate_from;      /* c, il primo indice delle iterate */
    long long step_from;         /* il primo n per cui vale f^{n+1} = f \circ f^{n} */
} Map;

extern const char *const operation_symbols[9];
extern Map maps[MAX_MAPS];
extern int map_count;
Map *map_find(int name);

/* Come sono messi in relazione i due membri di un enunciato. */
typedef enum { REL_EQ, REL_GE, REL_LE, REL_GT, REL_LT } Relation;

/* Un enunciato: membro sinistro, relazione, membro destro. */
typedef struct {
    Node *lhs, *rhs;
    Relation relation;
} Statement;

/* Un enunciato su una successione che l'enunciato stesso definisce per
 * ricorrenza: "se a_0 = 0 e a_{n+1} = \sqrt{6 + a_n}, allora a_n < 3". Le
 * ipotesi sono uguaglianze, i valori iniziali e la ricorrenza, più
 * eventualmente "n \ge q", che dice da quale n la ricorrenza vale; le tesi
 * sono confronti. Che le ipotesi definiscano davvero una successione lo
 * controlla il motore (capitolo 26): qui c'è solo com'è scritto. */
typedef struct {
    int givens;                    /* ipotesi valide in given[] */
    Statement given[MAX_GIVEN];    /* le uguaglianze, nell'ordine in cui sono scritte */
    int has_since;                 /* 1 se tra le ipotesi c'è "n \ge q" */
    int since_name;                /* la lettera n di quell'ipotesi */
    long long since;               /* il numero q */
    int claims;                    /* tesi valide in claim[] */
    Statement claim[MAX_CLAIMS];
} SequenceStatement;

/* Un enunciato sulla derivata di una funzione: "la derivata di ordine n di
 * function, rispetto a variable, è formula". L'ordine è una lettera, quella
 * su cui si fa induzione, e allora function non la contiene e formula di
 * solito sì; oppure è un numero. Senza formula è una richiesta: "calcola la
 * derivata di function" (27k). Gli alberi stanno nell'arena. */
typedef struct {
    int variable;     /* la lettera x rispetto a cui si deriva */
    int order;        /* la lettera n dell'ordine di derivazione, o 0 se è un numero */
    long long times;  /* l'ordine, quando è un numero: almeno 1 */
    Node *function;   /* la funzione da derivare */
    Node *formula;    /* ciò che l'enunciato dice della derivata; NULL in una richiesta */
} DerivativeStatement;

/* Che cosa un enunciato su un limite dice del limite (vedi LimitStatement):
 *   LIMIT_ASKED     niente, è una richiesta: "\lim_{x \to a} f";
 *   LIMIT_VALUE     che vale il numero `value`;
 *   LIMIT_PLUS      che vale +\infty;   LIMIT_MINUS  che vale -\infty;
 *   LIMIT_UNSIGNED  che vale \infty senza segno: |f| tende a +\infty;
 *   LIMIT_NONE      che non esiste: "\nexists \lim_{x \to a} f". */
typedef enum { LIMIT_ASKED, LIMIT_VALUE, LIMIT_PLUS, LIMIT_MINUS, LIMIT_UNSIGNED, LIMIT_NONE } LimitClaim;

/* Un enunciato su un limite: "il limite di function per variable che tende
 * al punto è ...". Il punto è un'espressione senza la variabile, oppure
 * +\infty o -\infty; il limite può essere da un lato solo. Gli alberi stanno
 * nell'arena; che il punto non contenga la variabile lo controlla il motore
 * (capitolo 29). */
typedef struct {
    int variable;         /* la lettera x che tende al punto */
    int sequence;         /* 1 se la lettera è n: un indice naturale, e il punto è +\infty */
    int infinity;         /* 0 per un punto finito, +1 per +\infty, -1 per -\infty */
    Node *point;          /* il punto finito, o NULL */
    int side;             /* +1 da destra (a^{+}), -1 da sinistra (a^{-}), 0 da tutte e due */
    Node *function;       /* la funzione di cui si fa il limite */
    LimitClaim claim;     /* che cosa l'enunciato ne dice */
    Node *value;          /* il valore, per LIMIT_VALUE; altrimenti NULL */
    const char *from, *to;  /* il testo "\lim_{...} f" nell'enunciato: [from, to) */
} LimitStatement;

/* Un enunciato su un integrale (9j): "l'integrale di integrand in
 * d variable è answer". Senza estremi è un integrale indefinito, e answer è
 * una primitiva F, scritta con la sua costante (F + c) che il lettore toglie;
 * con gli estremi è un integrale definito, e answer è un numero. Senza il
 * segno di uguale è una richiesta: answer è NULL, e la risposta la cerca il
 * motore (capitolo 30). Un estremo può essere +\infty o -\infty, e allora il
 * suo albero è NULL; un integrale definito può dire anche di valere
 * +\infty o -\infty, o di convergere (\in \mathbb{R}) o no (\notin
 * \mathbb{R}). Gli alberi stanno nell'arena. */
typedef struct {
    int variable;         /* la lettera x del differenziale dx */
    Node *integrand;      /* la funzione integranda, senza il dx */
    int definite;         /* 1 se ci sono gli estremi */
    Node *lower, *upper;  /* gli estremi finiti; NULL se l'integrale è indefinito, o l'estremo infinito */
    int lower_infinite, upper_infinite;  /* +1 per +\infty, -1 per -\infty, 0 per un estremo finito */
    Node *answer;         /* F senza la costante, oppure il valore; NULL per una richiesta */
    int answer_infinite;  /* +1 se l'enunciato dice "= +\infty", -1 se "= -\infty", altrimenti 0 */
    int membership;       /* +1 per "\in \mathbb{R}" (converge), -1 per "\notin \mathbb{R}", altrimenti 0 */
    int constant;         /* la lettera della costante di F, se c'è; altrimenti 0 */
} IntegralStatement;

/* Tipi di token. \left( e ( producono entrambi T_OPEN: per il valore assoluto
 * invece \left| e \right| restano distinti, perché una sbarra da sola non
 * dice se apre o chiude. */
typedef enum { T_END, T_NUM, T_LETTER, T_COMMAND, T_OPEN, T_CLOSE, T_ABS_OPEN, T_ABS_CLOSE, T_CHAR } TokenKind;

/* Il token corrente: l'unità che il parser guarda per decidere. */
typedef struct {
    TokenKind kind;
    long long value;    /* T_NUM */
    int digits;         /* T_NUM: numero di cifre */
    int ch;             /* T_LETTER, T_CHAR: il carattere */
    char name[24];      /* T_COMMAND: il nome senza barra */
    const char *start;  /* dove inizia nel testo */
} Token;

extern const char *cursor;
extern Token token;
extern const char *consumed;
extern const char *syntax_error;
void syntax(const char *message);
void next_token(void);
int is_char(int c);
int is_command(const char *name);

/* Lo stato del lettore di token. Rimetterlo com'era fa riprendere la lettura
 * da un punto precedente: serve dove un solo token non basta a decidere quale
 * regola della grammatica applicare (17c e 17d, e in 17r). I nodi creati nel
 * tentativo abbandonato restano nell'arena, inutilizzati. */
typedef struct {
    const char *cursor;
    Token token;
    const char *syntax_error;
} ParserState;

ParserState parser_save(void);
void parser_restore(ParserState state);
Node *node_new(NodeKind kind, Node *a, Node *b);
Node *node_num(long long value);
Node *node_call(Function fn, Node *a, Node *b);
int starts_with_derivative(const char *text);
Node *parse_expr(void);
Node *parse_expression(const char *text);
int parse_statement(const char *text, Statement *statement);
int parse_derivative_statement(const char *text, DerivativeStatement *out);
int starts_with_limit(const char *text);
int infinity_text(const char *from, const char *to);
int parse_limit_statement(const char *text, LimitStatement *out);
int node_is_factor(const Node *tree, const Node *target);
int starts_with_integral(const char *text);
int parse_integral_statement(const char *text, IntegralStatement *out);
int parse_sequence_statement(const char *text, SequenceStatement *out);

/* Tipi di nodo di un enunciato sugli insiemi.
 *
 * Warning: se aggiungi un tipo prima di SET_APPLY, aggiungi il ramo che lo
 * costruisce nel parser di questo capitolo, il suo tipo in set_check(), e il
 * suo case in member() o set_holds() (capitolo 15), in concrete() o
 * concrete_holds() e in put_set() (capitolo 16), e in parts_unfold() (17r).
 * SET_APPLY e SET_PAIR_IN sono della notazione dei libri (17r): li ha solo
 * l'enunciato com'è scritto, parts_unfold() li toglie, e i capitoli 15 e 16
 * li vedono solo in concrete() e concrete_holds(), per il controllo dello
 * svolgimento. */
typedef enum {
    SET_VAR,         /* una lettera: var è il suo indice */
    SET_EMPTY,       /* l'insieme vuoto */
    SET_ONLY_EMPTY,  /* la collezione il cui unico elemento è l'insieme vuoto */
    SET_POWER,       /* insieme delle parti di a */
    SET_UNION, SET_INTER, SET_DIFF, SET_SYMDIFF,  /* a op b */
    SET_PRODUCT,     /* a per b */
    SET_EQ, SET_SUBSET, SET_NEQ,                  /* relazioni tra a e b */
    SET_AND, SET_OR, SET_IMPLIES, SET_IFF,        /* connettivi tra a e b */
    SET_NOT,         /* non a */
    SET_EXISTS,      /* esiste un insieme, di indice var, tale che a */
    SET_APPLY,       /* 17r: l'applicazione di posto var in part_rules[]
                        applicata all'insieme a */
    SET_PAIR_IN      /* 17r: la coppia di insiemi (a, b) sta nella relazione
                        di posto var in part_rules[] */
} SetKind;

/* Il tipo di ciò che un nodo denota. TY_ANY è l'insieme vuoto, che può stare
 * al posto di un oggetto di qualunque tipo; TY_ERROR segnala operandi di tipo
 * sbagliato. */
typedef enum { TY_ERROR, TY_ANY, TY_SET, TY_FAMILY, TY_PAIRS, TY_FORMULA } SetType;

/* Un nodo dell'albero di un enunciato sugli insiemi. I nodi vivono nell'arena.
 * support e supports valgono solo per le relazioni e li riempie
 * relation_supports() (capitolo 15). */
typedef struct SetNode SetNode;
struct SetNode {
    SetKind kind;
    SetType type;       /* riempito da set_check() */
    int var;            /* SET_VAR, SET_EXISTS: indice in set_var_name */
    SetNode *a, *b;     /* operandi; NULL se non usati */
    unsigned *support;  /* configurazioni minime in cui la relazione fallisce */
    int supports;       /* quante sono */
};

extern int set_var_name[MAX_SET_LETTERS];
extern int set_var_count;
extern int parts_world;

/* 17r. Una relazione tra le parti di un insieme, G = \{(X, Y) \in
 * \mathcal{P}(S)^{2} \mid c\}, o un'applicazione di \mathcal{P}(S) in sé con
 * la sua regola, \forall X \in \mathcal{P}(S)\ (f(X) = e). È un nome per la
 * condizione c, o per l'espressione e, nelle lettere param[]: (A, B) \in G
 * vuol dire c con A e B al posto di X e Y, f(A) vuol dire e con A al posto
 * di X. Vedi la testa di 17r per le convenzioni.
 *
 * Invariante: rule non contiene quantificatori, quindi nessuna lettera degli
 * argomenti può esserne catturata; contiene solo le lettere param[] e quelle
 * libere dell'enunciato. */
typedef struct {
    int name;      /* la lettera G o f */
    int arity;     /* 2 per una relazione, 1 per un'applicazione */
    int param[2];  /* le lettere della regola: indici in set_var_name */
    int base;      /* l'insieme S, di cui sono parti gli argomenti */
    SetNode *rule; /* la condizione o l'espressione; NULL per un'applicazione
                      dichiarata di cui non si è ancora letta la regola */
} PartRule;

extern PartRule part_rules[MAX_PART_RULES];
extern int part_rule_count;
extern SetNode parts_declared;
SetNode *set_formula(void);
SetType set_join(SetType x, SetType y);
SetType set_check(SetNode *n);
extern SetNode *parts_to[MAX_SET_LETTERS];
SetNode *parts_unfold(const SetNode *n);
int parts_declaration_left(const SetNode *n);
void parts_reindex(SetNode *root, int *free_map);
int numbers_contain(const NumberSet *set, Frac value);
int numbers_equal(const NumberSet *a, const NumberSet *b);
int numbers_subset(const NumberSet *a, const NumberSet *b);
void numbers_sample(const NumberSet *set, Frac *out, int wanted);

/* Tipi di nodo di un enunciato con quantificatori.
 *
 * Warning: se aggiungi un tipo, aggiungi il ramo che lo costruisce nel parser
 * di questo capitolo, il suo case in formula_check(), in junction() o in
 * establish() (capitolo 18) e in sample_holds() (capitolo 19). La tabella
 * dei segni (18p) prende per un confronto ogni nodo che non sia un
 * connettivo: un tipo nuovo che non lo è va fermato prima, in
 * decide_quantified(), come F_IN e F_DIVIDES. */
typedef enum {
    F_EQUAL, F_DISTINCT,              /* left = right, left diverso da right */
    F_LESS, F_LESS_EQ,                /* left < right, left <= right: solo con la
                                         tabella dei segni (18p) */
    F_AND, F_OR, F_IMPLIES, F_IFF,    /* connettivi tra a e b */
    F_NOT,                            /* non a */
    F_FORALL, F_EXISTS,               /* per ogni / esiste variable in numbers: a */
    F_SOLVE,                          /* \{variable \in numbers \mid a\}: non è una
                                         condizione ma una domanda, "per quali
                                         valori vale a?", e sta solo in cima a
                                         un enunciato, o sotto il "per ogni" di
                                         un parametro (17h) */
    F_MAP,                            /* dichiarazione: di un'applicazione, di
                                         un'operazione o di una relazione data
                                         da una regola */
    F_IN,                             /* left appartiene a numbers (17k) */
    F_DIVIDES                         /* left divide right (17n) */
} FormulaKind;

/* Un nodo dell'albero di un enunciato con quantificatori: una condizione, cioè
 * qualcosa che può essere vero o falso. I campi non usati dal tipo sono NULL o
 * zero. I nodi vivono nell'arena.
 *
 * I campi da has_witness a quotient sono i soli scritti dopo il parsing: li
 * riempie la dimostrazione (capitolo 18), perché la verifica indipendente
 * (capitolo 19) possa ricontrollare ciò che ha scelto. Quando un "per ogni"
 * è dimostrato per casi sul resto (regola 18o), il valore scelto per un
 * "esiste" al suo
 * interno cambia da un caso all'altro: per questo i valori sono MAX_CASES, e
 * fuori da una dimostrazione per casi si usa il primo. */
typedef struct Formula Formula;
struct Formula {
    FormulaKind kind;
    Node *left, *right;       /* i confronti (da F_EQUAL a F_LESS_EQ): i due membri.
                                 F_IN: left è l'espressione, right è NULL.
                                 F_DIVIDES: left è il divisore, right ciò che
                                 divide */
    int swapped;              /* F_LESS, F_LESS_EQ: 1 se nell'enunciato c'era > o
                                 \ge, e quindi left è il membro scritto a destra.
                                 Serve solo a chi deve mostrare i membri com'erano
                                 scritti (il grafico, 18q). F_IN, F_DIVIDES: 1
                                 se c'era \notin o \nmid, e la condizione è la
                                 negazione */
    Formula *a, *b;           /* le condizioni componenti */
    int variable;             /* F_FORALL, F_EXISTS, F_SOLVE: la lettera legata */
    NumberSet numbers;        /* F_FORALL, F_EXISTS, F_SOLVE: l'insieme su cui varia.
                                 F_IN: l'insieme a cui left appartiene */
    const char *start, *end;  /* com'è scritto nell'enunciato: [start, end) */
    unsigned has_witness;     /* il bit r dice se witness[r] è stato scelto */
    Rat witness[MAX_CASES];   /* il valore scelto per variable nel caso r: un
                                 numero, o un'espressione nelle variabili più
                                 esterne */
    int modulus;              /* F_FORALL dimostrato per casi sul resto: il
                                 modulo m; altrimenti 0 */
    int quotient;             /* e la lettera t di variable = m t + r */
    int pair;                 /* 17t-2. F_FORALL, F_EXISTS: se variable è la
                                 prima componente di una coppia, la lettera
                                 della coppia (la seconda componente è la
                                 variabile del nodo a); altrimenti 0 */
    int complex;              /* 17t-4: con pair, 1 se la coppia è un numero
                                 complesso, parte reale e coefficiente di i */
};

/* Una variabile quantificata e l'insieme su cui varia. */
typedef struct {
    int name;                  /* la lettera */
    const NumberSet *numbers;  /* l'insieme: sta nel nodo del quantificatore */
} Bound;

Formula *formula_node(FormulaKind kind, Formula *a, Formula *b, const char *start);
extern int scope_count;
extern int pair_set_count;
int fresh_letter(void);
extern char draft[4 * MAX_FORMULA];
extern size_t draft_length;
void draft_rewrite(const char *start, const char *end, const int *from, const char *const *to, int count);
Formula *unfold(void);
int node_is_numeral(const Node *node);
Node *node_substitute(const Node *node, const int *from, const Node *const *to, int count);
Formula *formula_substitute(const Formula *f, const int *from, const Node *const *to, int count);

/* 17t-2. Una lettera che sta per una coppia di numeri, e le sue componenti.
 * Si riconosce dal quantificatore: bound è l'insieme della sua variabile in
 * scope[], che per una coppia resta vuoto (start NULL), e identifica il
 * quantificatore finché è in vista. Le componenti sono lettere nuove. */
typedef struct {
    int letter;              /* la lettera della coppia */
    const NumberSet *bound;  /* l'insieme della sua variabile in scope[] */
    int part[2];             /* le lettere delle due componenti */
    NumberSet numbers[2];    /* i loro insiemi */
    int complex;             /* 17t-4: 1 se la coppia è un numero complesso */
} PairVariable;

extern PairVariable pairs_seen[2 * MAX_PAIR_VARIABLES];
extern int pairs_seen_count;
extern char pairs_note[200];
void pairs_note_write(void);
Formula *logic_formula(void);
Formula *logic_statement(void);
extern int quantifier_depth;
int term_is_rational(const Node *node);
void formula_check(const Formula *f);
extern Bound statement_parameters[MAX_PARAMETERS];
extern int statement_parameter_count;
void scope_parameters(void);
Node *node_replaced(Node *tree, const Node *target, Node *by);
extern char unshadowed_note[200];
void parameters_unshadowed(Formula *f);
void read_definitions(const Formula *f);
void pair_sets_check(void);

/* Il "tipo" di ciò che vale vero o falso: il valore di una parte o di una
 * relazione applicata ai suoi argomenti. Non è un insieme dell'enunciato:
 * ha un tag distinto da ogni indice di insieme rappresentabile. */
#define TRUTH INT_MAX

extern const char *const greek_letters[22];

/* Un simbolo di cui l'enunciato parla senza darne una regola: un elemento
 * con un nome, un'applicazione, un'operazione, una parte di un insieme o una
 * relazione. Anche gli elementi a cui la dimostrazione dà un nome (capitolo
 * 28) sono simboli, aggiunti in coda.
 *
 * Invariante: due simboli diversi non hanno lo stesso nome e lo stesso
 * pedice. */
typedef struct {
    int name;       /* Lettera o codice positivo di operazione, greco, relazione
                       o numero; -1 meno l'indice di insieme per una struttura. */
    int index;      /* 0 senza pedice, ZERO_INDEX per zero, positivo per un numero,
                       LETTER_INDEX meno la lettera per un pedice letterale */
    int arity;      /* quanti argomenti: 0 per un elemento, 1 o 2 */
    int domain[2];  /* l'insieme di ogni argomento: un posto in sort_data[] */
    int range;      /* l'insieme del valore, o TRUTH per parti e relazioni */
    int family;     /* 1 per una famiglia di parti X_{i} (17p): una relazione
                       tra un insieme e quello degli indici, che si scrive
                       x \in X_{i} e non (x, i) \in X */
    int paired;     /* 17p: un'applicazione f a valori in un prodotto,
                       f \colon S \to T \times V, sono due applicazioni, le
                       sue componenti f_{1} e f_{2}: 1 o 2 per quelle, 0 per
                       ogni altro simbolo */
} Symbol;

extern Symbol *symbols;
extern int symbol_count;
extern int sort_count;

/* 17v. Che cosa è l'insieme di posto i. Quasi sempre un insieme qualsiasi,
 * con il nome di una lettera; ma può essere anche l'insieme delle parti di
 * un altro, \mathcal{P}(S), o l'insieme delle applicazioni tra due, T^{S},
 * presi come insiemi di oggetti (vedi la testa di 17v). Un insieme di questi
 * due tipi non ha una lettera (sort_data[i].name è 0) e ha un simbolo di
 * struttura, che dice che cosa sono i suoi elementi: l'appartenenza "t sta
 * nella parte X" o l'applicazione "f applicata a x".
 *
 * Warning: se aggiungi un tipo, aggiungi il suo nome in put_sort(),
 * put_model_element() e cert_sort(), la sua grandezza in model_sizes() e
 * le sue tabelle in model_structure() (28m), la sua voce in
 * cert_abstract_head(), e la sua lettura al verificatore (ck_derived_sort()
 * e ck_numbers_sort() in checker.c). */
typedef enum {
    SORT_PLAIN,   /* un insieme qualsiasi, di nome sort_data[i].name */
    SORT_PARTS,   /* le parti di sort_data[i].base */
    SORT_MAPS,    /* le applicazioni da sort_data[i].base a sort_data[i].target */
    SORT_NUMBERS  /* i numeri scritti nell'enunciato, come elementi di una
                     relazione data da un elenco di coppie: ognuno è un
                     elemento con un nome (numeral_symbol()), tutti diversi,
                     e non ce ne sono altri */
} SortKind;
/* Un insieme dell'enunciato, identificato dal suo indice nel vettore.
 * Le dipendenze base/target precedono sempre l'insieme derivato; nessun
 * nodo conserva indirizzi nel vettore che puo essere riallocato. */
typedef struct {
    int name;       /* Lettera maiuscola per SORT_PLAIN, zero per gli altri. */
    int index;      /* Pedice numerico del nome, zero se assente. */
    SortKind kind;  /* Insieme arbitrario, parti, mappe o numeri scritti. */
    int base;       /* Dominio di una costruzione derivata, -1 se assente. */
    int target;     /* Codominio delle mappe, -1 negli altri casi. */
    int symbol;     /* Simbolo di appartenenza o valutazione, -1 se assente. */
} SortData;

extern SortData *sort_data;

/* 17u. Che cosa è il simbolo di posto i rispetto ai quantificatori su parti.
 * PART_FREE: un simbolo dichiarato, o un nome dato dalla dimostrazione.
 * PART_BOUND: la parte legata da un \forall X \subseteq S o da un \exists X
 * \subseteq S, il cui nome è in vista mentre si legge la condizione del
 * quantificatore. PART_HIDDEN: la stessa, dopo; il nome non vuol più dire
 * nulla, e la stessa lettera può legare un'altra parte. Una parte legata non
 * è dichiarata: non ha una tabella nei modelli né una voce symbol nel
 * certificato. */
enum { PART_FREE, PART_BOUND, PART_HIDDEN };

extern int *symbol_bound;

/* Un'espressione che indica un elemento: una variabile, oppure un simbolo
 * applicato ai suoi argomenti (nessuno, per un elemento con un nome). Per
 * una parte o una relazione applicata, il "valore" è vero o falso. I nodi
 * vivono nell'arena. */
typedef struct Elem Elem;
struct Elem {
    int symbol;    /* il simbolo, posto in symbols[]; -1 per una variabile */
    int slot;      /* variabile: il suo posto nel vettore slot_data */
    Elem *arg[2];  /* gli argomenti; NULL dove non servono */
};

/* Tipi di nodo di un enunciato su insiemi qualsiasi.
 *
 * Warning: se aggiungi un tipo prima di S_MEMBER, aggiungi il ramo che lo
 * costruisce nel lettore di questo paragrafo e i suoi casi nel capitolo 28:
 * in model_holds(), in known_open(), in truth(), in put_sentence() e in
 * cert_sentence(), e la sua parola al lettore del verificatore (capitolo 11
 * di checker.c); e il suo caso in unfold_sentence() (17q) e in book_holds()
 * (28h). Un tipo senza componenti a e b, come S_EQUIPOTENT (17w), va anche
 * tra quelli che sentence_ground(), instance_rewrite() e instance_survey()
 * non attraversano. Un tipo da S_MEMBER in poi è invece della notazione dei
 * libri (17p): va in unfold_sentence(), che lo traduce nei primi, e in
 * book_holds(), e il capitolo 28 non lo vede mai. */
typedef enum {
    S_TRUE,                         /* una dichiarazione: non afferma nulla */
    S_EQUAL,                        /* left = right */
    S_HOLDS,                        /* left, una parte o una relazione
                                       applicata, vale */
    S_NOT,                          /* non a */
    S_AND, S_OR, S_IMPLIES, S_IFF,  /* connettivi tra a e b */
    S_FORALL, S_EXISTS,             /* per ogni / esiste un elemento, la
                                       variabile di posto slot: a */
    S_FORALL_PART, S_EXISTS_PART,   /* 17u: per ogni / esiste una parte, il
                                       simbolo legato part: a */
    S_EQUIPOTENT,                   /* 17w: i due lati, prodotti di insiemi
                                       (side_slot[]), sono equipotenti */
    S_MEMBER,                       /* 17p: gli elementi item[] stanno
                                       nell'insieme set */
    S_INCLUDED,                     /* 17p: set è contenuto in other, e se
                                       proper non è uguale a other */
    S_SAME,                         /* 17p: set e other sono lo stesso insieme */
    S_UNIQUE,                       /* 17p: esiste un solo elemento, la
                                       variabile di posto slot, tale che a */
    S_COUNT                         /* 17x: l'insieme set ha almeno least
                                       elementi e, se most >= 0, al più most */
} SentenceKind;

/* Un insieme di elementi o di coppie scritto come nei libri: è definito
 * nel paragrafo 17p, dove si legge. */
typedef struct SetTerm SetTerm;

/* Un nodo dell'albero di un enunciato su insiemi qualsiasi: una condizione.
 * I campi non usati dal tipo sono NULL o zero. I nodi vivono nell'arena. */
typedef struct Sentence Sentence;
struct Sentence {
    SentenceKind kind;
    Elem *left, *right;          /* S_EQUAL: i due membri. S_HOLDS: left */
    Sentence *a, *b;             /* le condizioni componenti */
    int slot;                    /* S_FORALL, S_EXISTS, S_UNIQUE: la
                                    variabile legata */
    const char *start, *end;     /* com'è scritto nell'enunciato: [start, end) */
    const SetTerm *set, *other;  /* S_MEMBER: set. S_INCLUDED, S_SAME: i due
                                    insiemi */
    Elem *item[MAX_ARITY];       /* S_MEMBER: il membro, una componente per
                                    posto */
    int items;                   /* S_MEMBER: quante componenti */
    int proper;                  /* S_INCLUDED: 1 per l'inclusione propria,
                                    \subsetneq */
    int part;                    /* S_FORALL_PART, S_EXISTS_PART (17u): la
                                    parte legata, un posto in symbols[] */
    int side_slot[2][2];         /* S_EQUIPOTENT (17w): per ogni lato, una
                                    variabile per componente, nel suo insieme
                                    (slot_data): le usano le identità di due
                                    applicazioni inverse (28q) */
    int sides[2];                /* S_EQUIPOTENT: le componenti di ogni lato,
                                    1 o 2 */
    int least, most;             /* S_COUNT (17x): quanti elementi ha almeno
                                    l'insieme set (0 o più), e quanti al più;
                                    most = -1 se non c'è un massimo */
};

/* Una variabile astratta, riconosciuta dal suo posto e non dal nome.
 * letter e index sono i codici della lettera e del pedice (zero se assente);
 * sort e l'insieme, -1 finche l'uso non lo determina; pair e il posto della
 * seconda componente se questa e la prima di una coppia, -1 altrimenti.
 * Il vettore globale possiede le celle; nessun nodo conserva indirizzi al
 * suo interno, perche una crescita puo spostarlo. */
typedef struct { int letter, index, sort, pair; } SlotState;

extern SlotState *slot_data;
extern size_t slot_capacity, unfold_capacity;
extern int slot_count;
extern Elem **unfold_to;
extern int abstract_example;
int symbol_find(int name, int index);
int symbol_append(Symbol symbol);
extern const char *const relation_commands[3];
int abstract_name(int *index);
int sort_derived_find(SortKind kind, int base, int target);
int symbol_structure(int symbol);
Elem *elem_new(int symbol, int slot, Elem *a, Elem *b);
int elem_sort(const Elem *e);
Sentence *sentence_new(SentenceKind kind, Sentence *a, Sentence *b, const char *start);
extern const SetTerm *part_template[MAX_TEMPLATES];
extern int part_template_count;
int slot_new(int letter, int index, int sort);

/* Tipi di termine d'insieme.
 *
 * Warning: se aggiungi un tipo, aggiungi il ramo che lo legge in
 * abstract_set_factor(), il suo svolgimento in unfold_member() (17q) e il
 * suo calcolo in book_member() (28h). */
typedef enum {
    ST_SYMBOL,      /* una parte o una relazione dichiarata: symbol */
    ST_SECTION,     /* X_{i}: ciò che la famiglia symbol mette in relazione con
                       l'indice item[0] */
    ST_SORT,        /* un insieme qualsiasi, tutto: sort[0] */
    ST_EMPTY,       /* l'insieme vuoto */
    ST_LIST,        /* \{item[0], ..., item[items - 1]\} */
    ST_BUILDER,     /* \{schema | condition\}: lo schema è item[], una variabile
                       per componente; le variabili, senza ripetizioni, bound[] */
    ST_IMAGE,       /* l'immagine di a attraverso l'applicazione symbol; con
                       items = 1 (17v) l'applicazione è l'elemento item[0] di un
                       insieme T^{S}, e symbol è il simbolo di struttura */
    ST_PREIMAGE,    /* la controimmagine di a, allo stesso modo */
    ST_UNION, ST_INTER, ST_DIFF, ST_SYMDIFF,  /* a op b */
    ST_BIG_UNION,   /* l'unione degli a al variare dell'indice, la variabile
                       bound[0]; se symbol >= 0 l'indice varia nella parte
                       symbol, se b c'è (17v) nell'insieme b */
    ST_BIG_INTER,   /* l'intersezione, allo stesso modo */
    ST_PART,        /* 17v: l'elemento item[0] di un insieme \mathcal{P}(S),
                       preso come la parte di S che è; symbol è l'appartenenza */
    ST_POWERSET,    /* 17v: \mathcal{P}(a), le parti contenute in a, come
                       elementi di \mathcal{P}(S); symbol è l'appartenenza */
    ST_DESCRIBE,    /* 17v: l'insieme b, in cui la variabile bound[0], una
                       parte, è la parte uguale all'insieme a: t vi sta se
                       \forall Z\ (Z = a \implies t \in b). Lo crea un elenco
                       di parti scritte come insiemi, \{\emptyset\} */
    ST_REPLACE,     /* 17v: \{E \mid C\}, gli E al variare delle variabili
                       bound[] che rendono vera condition. E è l'insieme a,
                       e i membri sono parti; oppure, con items = 1, è
                       l'elemento item[0] */
    ST_TUPLES       /* 17v: un elenco di items membri di arity componenti,
                       \{(1, 1), (1, 2)\}: la componente i del membro k è
                       tuple[k * arity + i] */
} SetTermKind;

/* Un termine d'insieme (17p): un insieme di elementi o di coppie scritto
 * come nei libri. I suoi membri hanno `arity` componenti, la componente i
 * nell'insieme sort[i] (un posto in sort_data[]). arity è 0 solo per un
 * insieme vuoto che non è ancora stato confrontato con nulla. I campi non
 * usati dal tipo sono zero, symbol è -1. I nodi vivono nell'arena e non
 * cambiano dopo la lettura: un termine definito si usa dove serve senza
 * copiarlo. */
struct SetTerm {
    SetTermKind kind;
    int arity;
    int sort[MAX_ARITY];
    int symbol;             /* vedi i tipi; -1 dove non serve */
    SetTerm *a, *b;         /* gli operandi */
    Elem *item[MAX_ARITY];  /* ST_LIST: gli elementi. ST_SECTION: l'indice.
                               ST_BUILDER: lo schema */
    int items;
    int bound[MAX_ARITY];   /* ST_BUILDER: le variabili dello schema.
                               ST_BIG_*: l'indice, in bound[0] */
    int bounds;
    Sentence *condition;    /* ST_BUILDER: la condizione */
    Elem **tuple;           /* 17v, ST_TUPLES: i membri, nell'arena */
};

extern const char *const equipotence_exponent_reason;
int equipotence_bad_exponent(const char *formula);
extern const char count_reason[];
extern int count_met;
Sentence *abstract_statement(void);
extern int unfold_copying;
int unfold_slot(int sort);
Sentence *unfold_member(Elem *const *t, const SetTerm *set, const Sentence *from);
int sentence_has_book_notation(const Sentence *s);
Sentence *abstract_unfold(const Sentence *root);

/* Tipi di nodo di un'espressione tra matrici. Tra parentesi i campi usati.
 *
 * Warning: se aggiungi un tipo, aggiungi il suo caso in matrix_eval() e in
 * matrix_cert_node() (capitolo 32 del motore), e la sua parola nel capitolo
 * 17 di checker.c. */
typedef enum {
    M_SCALAR,     /* un numero: scalar, la sua espressione */
    M_TABLE,      /* una matrice scritta: rows, cols, entry */
    M_IDENTITY,   /* l'identità: rows, la dimensione; 0 se è scritta senza pedice */
    M_NEG,        /* -a */
    M_ADD,        /* a + b */
    M_SUB,        /* a - b */
    M_MUL,        /* a b */
    M_POWER,      /* a elevata all'intero power, anche negativo o zero */
    M_TRANSPOSE,  /* la trasposta di a */
    M_DET,        /* il determinante di a */
    M_RANK,       /* il rango di a */
    M_TRACE       /* la traccia di a */
} MatrixKind;

/* Un nodo dell'albero di un'espressione tra matrici: una sua
 * sotto-espressione, che vale una matrice oppure un numero. Quale delle due
 * lo stabilisce il motore calcolandola: l'albero registra solo com'è
 * scritta. I nodi stanno nell'arena; i campi che il tipo non usa sono zero.
 *
 * Un nome definito dall'enunciato non ha un nodo suo: dove compare c'è
 * l'albero della sua definizione, lo stesso nodo ogni volta. L'albero è
 * quindi un grafo senza cicli, e chi lo visita può passare più volte dallo
 * stesso nodo. */
typedef struct MatrixNode MatrixNode;
struct MatrixNode {
    MatrixKind kind;
    MatrixNode *a, *b;  /* gli operandi */
    Node *scalar;       /* M_SCALAR: l'espressione del numero (capitolo 8) */
    int rows, cols;     /* M_TABLE: righe e colonne, almeno 1. M_IDENTITY: rows è la
                           dimensione; se vale 0 la mette il motore, quando il
                           contesto la fissa (32d) */
    Node **entry;       /* M_TABLE: le rows * cols espressioni degli elementi, per righe */
    long long power;    /* M_POWER: l'esponente */
};

/* Come sono messi in relazione i due membri di un enunciato sulle matrici;
 * MATRIX_ASKED se il secondo membro non c'è, ed è una richiesta. */
typedef enum { MATRIX_ASKED, MATRIX_EQ, MATRIX_NEQ, MATRIX_LT, MATRIX_LE, MATRIX_GT, MATRIX_GE } MatrixRelation;

/* Un enunciato sulle matrici: i due membri e la loro relazione, con i nomi
 * già sostituiti dalle definizioni. In una richiesta right è NULL. Le
 * definizioni restano anche da sole, nell'ordine in cui sono scritte: il
 * motore controlla che ognuna abbia un valore, anche se nessuno la usa. */
typedef struct {
    MatrixNode *left, *right;
    MatrixRelation relation;
    int definitions;             /* definizioni valide in definition[] */
    MatrixNode *definition[26];  /* gli alberi delle matrici con un nome: al più una per lettera */
} MatrixStatement;

struct matrix_environments { const char *name; int determinant, columns; };
extern const struct matrix_environments matrix_environments[5];
MatrixNode *matrix_node(MatrixKind kind, MatrixNode *a, MatrixNode *b);
int matrix_function(MatrixKind *kind);
MatrixNode *matrix_factor(void);
void matrix_start(const char *text);
void matrix_definitions(MatrixStatement *out);
int matrix_starts_here(void);
int parse_matrix_statement(const char *text, MatrixStatement *out);

#define MAX_UNKNOWNS 12          /* incognite di un sistema; parametri e addendi di un insieme scritto */
#define MAX_SYSTEM_EQUATIONS 16  /* equazioni di un sistema */

/* Una lettera di un sistema: un'incognita, o un parametro di un insieme
 * scritto. È una minuscola, con il suo pedice numerico se ne ha uno: index
 * vale -1 per x, 1 per x_{1}. */
typedef struct {
    int name;
    long long index;
} LinearLetter;

/* Un addendo di un vettore scritto: una tupla, moltiplicata per un numero se
 * factor non è NULL, e sottratta invece che sommata se negative vale 1. */
typedef struct {
    Node *factor;
    int negative;
    Node **entry;  /* le componenti della tupla: quante dice VectorSum.size; nell'arena */
} VectorTerm;

/* Un vettore di \mathbb{R}^{size} scritto come somma di tuple: un punto, o
 * l'elemento generico di un insieme scritto, e allora nelle sue espressioni
 * compaiono i parametri dell'insieme. */
typedef struct {
    int size;   /* le componenti di ogni tupla, almeno 2 */
    int terms;  /* addendi validi in term[] */
    VectorTerm term[MAX_UNKNOWNS + 1];
} VectorSum;

/* Come un enunciato parla dell'insieme delle soluzioni di un sistema;
 * LINEAR_ASKED se non dice nulla: è una richiesta. */
typedef enum { LINEAR_ASKED, LINEAR_EQ, LINEAR_NEQ, LINEAR_IN, LINEAR_NOTIN } LinearRelation;

/* Un enunciato sull'insieme delle soluzioni di un sistema lineare: il
 * sistema, e che cosa se ne dice.
 *
 * Il sistema ha due scritture. Con vector a 0 le incognite sono lettere, e
 * le equazioni sono coppie di espressioni del capitolo 9. Con vector a 1
 * l'incognita è una sola, unknown[0], ed è un vettore: l'unica equazione è
 * tra due espressioni del capitolo 31, matrix_left e matrix_right. In tutti
 * e due i casi dimension è l'esponente di \mathbb{R}: il numero delle
 * incognite, o delle componenti del vettore. */
typedef struct {
    int dimension;
    int vector;
    int unknowns;                         /* lettere valide in unknown[]: dimension, oppure 1 */
    LinearLetter unknown[MAX_UNKNOWNS];
    int equations;                        /* con vector a 0: le equazioni valide in left[] e right[] */
    Node *left[MAX_SYSTEM_EQUATIONS], *right[MAX_SYSTEM_EQUATIONS];
    MatrixNode *matrix_left, *matrix_right;
    LinearRelation relation;
    int empty;                            /* LINEAR_EQ, LINEAR_NEQ: 1 se l'insieme scritto è \emptyset */
    VectorSum stated;                     /* LINEAR_EQ, LINEAR_NEQ senza empty: l'elemento generico dell'insieme
                                             scritto; LINEAR_IN, LINEAR_NOTIN: il vettore di cui si parla */
    int parameters;                       /* i parametri dell'insieme scritto, validi in parameter[] */
    LinearLetter parameter[MAX_UNKNOWNS];
    const char *set_start, *set_end;      /* dov'è scritto l'insieme delle soluzioni: [set_start, set_end) */
} LinearStatement;

void linear_reals(void);
void linear_unknowns(LinearStatement *st);
void linear_fact(LinearStatement *st);
int parse_linear_statement(const char *text, LinearStatement *st, MatrixStatement *names);
char *read_file(const char *path);

/* Un enunciato letto da un \item: la formula e ciò che il testo dice su dove
 * parte l'induzione. formula e presa in prestito dal deposito del lettore,
 * fino alla successiva read_item; chi la conserva deve copiarla. */
typedef struct {
    const char *formula;        /* formula LaTeX terminata da '\0', presa in prestito */
    int variable;               /* variabile di induzione */
    int has_base;               /* 1 se il testo indica il caso base */
    int conditional;            /* 1 se il testo pone una condizione non letta */
    int remark;                 /* 1 se un inciso tra parentesi è stato letto come commento */
    long long base;             /* il caso base, se has_base */
} Item;

int next_item(const char **position, const char **item, const char **end);
const char *read_item(const char *item, const char *end, Item *out);

#define MAX_FUNCTIONS 4            /* funzioni dichiarate da un enunciato */
#define MAX_FUNCTION_VARIABLES 4   /* variabili di una funzione dichiarata */
#define MAX_PARTIAL_ORDER 4        /* ordine di una derivata parziale */
#define MAX_OPERANDS 32            /* derivate e funzioni scritte in un enunciato */
#define MAX_PARTIAL_CLAIMS 20      /* tesi, una per componente: il gradiente e l'hessiana di una funzione di 4 variabili */

/* Il nome interno, fuori dai caratteri e dagli altri nomi interni (capitolo
 * 1 del motore), della variabile che tiene il posto dell'operando numero 0;
 * gli altri seguono. */
#define VAR_OPERAND 6400

/* Una funzione dichiarata dall'enunciato: "f(x, y) = x^{2} y". Serve a dare
 * un nome all'espressione di cui l'enunciato scrive le derivate, e a dire
 * quali sono le sue variabili e in che ordine: l'ordine delle componenti del
 * gradiente e delle coordinate di un punto. Le altre lettere di body sono
 * parametri. Invariante: le lettere di variable[] sono tutte diverse, e
 * nessuna è il nome di una funzione dichiarata o la lettera e. */
typedef struct {
    int name;                              /* la lettera f */
    int variables;                         /* quante variabili ha: da 1 a MAX_FUNCTION_VARIABLES */
    int variable[MAX_FUNCTION_VARIABLES];  /* le loro lettere, nell'ordine in cui sono scritte */
    Node *body;                            /* l'espressione che la definisce, nell'arena */
} DeclaredFunction;

/* Un operando: una derivata parziale scritta nell'enunciato, o una funzione
 * dichiarata usata in un'espressione (una derivata di ordine 0), se serve
 * calcolata in un punto. Invariante: con function = -1 non c'è un punto, e
 * nessuna lettera di by[] è la lettera e. */
typedef struct {
    int function;                         /* la funzione dichiarata, come indice in PartialStatement.function[]; -1 se la funzione è body */
    Node *body;                           /* con function = -1 l'espressione scritta dopo il segno; altrimenti NULL */
    int order;                            /* quante volte si deriva: da 0 a MAX_PARTIAL_ORDER */
    int by[MAX_PARTIAL_ORDER];            /* le lettere rispetto a cui si deriva, nell'ordine in cui si deriva */
    int at;                               /* 1 se la derivata è calcolata in un punto */
    Node *point[MAX_FUNCTION_VARIABLES];  /* con at = 1 le coordinate, una per variabile della funzione, nel suo ordine */
} PartialOperand;

/* Che cosa chiede un enunciato senza il segno di uguale: nulla (è
 * un'affermazione), il valore di un'espressione, un gradiente, un'hessiana,
 * oppure i punti critici di una funzione. Per le prime tre richieste dice in
 * che forma va scritta la risposta; l'ultima è del capitolo 36 del motore. */
typedef enum { ASKED_NOTHING, ASKED_VALUE, ASKED_GRADIENT, ASKED_HESSIAN, ASKED_CRITICAL } PartialRequest;

/* Come sono messi in relazione i due membri di una tesi. Non è la Relation
 * del capitolo 8, che non ha il "diverso". */
typedef enum { CLAIM_EQ, CLAIM_NEQ, CLAIM_LT, CLAIM_LE, CLAIM_GT, CLAIM_GE } ClaimRelation;

/* Le scritture della definitezza di un'hessiana che un enunciato può
 * contenere, come bit di PartialStatement.definite: quelle con il segno
 * stretto (\succ, \prec), svolte nei minori principali di testa, e quelle
 * con il segno largo (\succeq, \preceq), svolte in tutti i minori principali
 * (34s). */
#define DEFINITE_STRICT 1
#define DEFINITE_WEAK 2

/* Una tesi di un enunciato sulle funzioni di più variabili: due espressioni,
 * in cui gli operandi compaiono come variabili (VAR_OPERAND + indice), e la
 * loro relazione, com'è scritta (a > b resta a > b: la dimostrazione la
 * riporta così). In una richiesta rhs è NULL e relation non conta. */
typedef struct {
    Node *lhs, *rhs;
    ClaimRelation relation;
} PartialClaim;

/* Un enunciato sulle funzioni di più variabili, com'è scritto: le funzioni
 * dichiarate, gli operandi, e le tesi. Un gradiente o un'hessiana sono già
 * svolti: una tesi per componente, riga per riga. In una richiesta le tesi
 * hanno solo il primo membro (rhs è NULL), e sono le componenti di ciò che
 * si chiede: per i punti critici, quelle del gradiente. Gli alberi stanno
 * nell'arena. */
typedef struct {
    int functions;                          /* funzioni valide in function[] */
    DeclaredFunction function[MAX_FUNCTIONS];
    int operands;                           /* operandi validi in operand[] */
    PartialOperand operand[MAX_OPERANDS];
    int claims;                             /* tesi valide in claim[] */
    PartialClaim claim[MAX_PARTIAL_CLAIMS];
    PartialRequest request;                 /* ASKED_NOTHING, o la forma della risposta chiesta */
    int columns;                            /* in una richiesta: le colonne della risposta (le righe sono claims / columns) */
    const char *asked_from, *asked_to;      /* in una richiesta: il testo di ciò che si chiede, [from, to) nell'enunciato */
    int critical;                           /* ASKED_CRITICAL: la funzione di cui si chiedono i punti critici, come indice in function[] */
    int determinant;                        /* 1 se l'enunciato scrive un determinante: la dimostrazione dice allora che cosa se ne conclude (35g) */
    int definite;                           /* le scritture della definitezza lette (34s): DEFINITE_STRICT, DEFINITE_WEAK, la loro somma, o 0.
                                               Il verdetto e la dimostrazione dicono allora che cosa abbreviavano */
} PartialStatement;

int starts_with_definition(const char *text);
int parse_partial_statement(const char *text, PartialStatement *out);

/* Un insieme di lettere usate come indici: il bit di posto index_slot(c)
 * dice se la lettera c ne fa parte. Le lettere latine sono 52. */
typedef unsigned long long IndexSet;
#define INDEX_LETTERS 52

int index_slot(int letter);
int index_letter(int slot);
int index_first_slot(IndexSet set);

/* Tipi di nodo di un'espressione con gli indici.
 *
 * Warning: se aggiungi un tipo, aggiungi il suo caso in index_scan() (37c)
 * e, nel motore, in index_value() (38c) e in index_cert() (38e); se è un
 * simbolo con gli indici, anche in index_is_leaf(), in index_leaf() (38a),
 * in index_positions() e in index_unfold() (capitolo 39). Il verificatore ha la
 * sua notazione e il suo lettore (capitolo 19 di checker.c): un tipo nuovo
 * va aggiunto anche lì, con la sua giustificazione. */
typedef enum {
    IX_NUM,      /* un numero razionale: number */
    IX_DELTA,    /* la delta di Kronecker: due indici */
    IX_EPSILON,  /* il simbolo di Levi-Civita: rank indici */
    IX_TENSOR,   /* una componente del tensore name: rank indici, anche zero */
    IX_METRIC,   /* la metrica dichiarata, com'è scritta (capitolo 39): due
                    indici, in basso, in alto o uno e uno */
    IX_LOWER,    /* la metrica con i due indici in basso, dopo lo svolgimento
                    (39c): c_i se i due indici coincidono, 0 altrimenti */
    IX_UPPER,    /* la sua inversa, con i due indici in alto: 1/c_i o 0 */
    IX_NEG,      /* -a */
    IX_ADD,      /* a + b */
    IX_SUB,      /* a - b */
    IX_MUL       /* a b */
} IndexKind;

/* Un nodo dell'albero di un'espressione con gli indici: una sotto-espressione
 * dell'identità. Sta nell'arena, come i suoi vettori.
 *
 * index[] e upper[] descrivono gli indici di un simbolo, nell'ordine in cui
 * sono scritti: una lettera vale il suo carattere (per una lettera greca,
 * quello della latina che la rappresenta, 37f), un numero vale sé stesso, e
 * i due casi non si confondono perché un numero è una cifra o al più 10 e
 * ogni lettera vale almeno 'A'. Mentre si legge il numero è la cifra
 * scritta; a enunciato finito è il valore da 1 a d (37d). I tre insiemi li
 * calcola index_scan() (37c). Gli ultimi tre campi
 * sono annotazioni lasciate dal motore (38b nel motore): il lettore li lascia
 * a zero. */
typedef struct IndexNode IndexNode;
struct IndexNode {
    IndexKind kind;
    IndexNode *a, *b;      /* i figli: IX_NEG ha solo a, le foglie nessuno */
    Frac number;           /* IX_NUM: il valore */
    int name;              /* IX_TENSOR: la lettera che lo nomina */
    int rank;              /* simboli: quanti indici */
    int *index;            /* simboli: gli indici */
    unsigned char *upper;  /* simboli: 1 per un indice scritto in alto */
    IndexSet free;         /* le lettere libere: compaiono una volta sola */
    IndexSet bound;        /* le lettere sommate nel nodo o più in basso */
    IndexSet here;         /* le lettere sommate proprio in questo nodo */
    IndexSet up;           /* con una metrica (39b): le lettere libere scritte in alto */
    IndexNode **factor;    /* motore: i fattori del prodotto che comincia qui */
    int factors;           /* motore: quanti sono */
    IndexSet sum;          /* motore: le lettere sommate in quel prodotto */
};

/* Un'identità con gli indici, letta e controllata: i due membri, la
 * dimensione, gli indici liberi (gli stessi nei due membri) e, per ogni
 * lettera, il rango del tensore che nomina: rank[index_slot(c)] è il numero
 * dei suoi indici, o -1 se c non è il nome di un tensore. Con delle ipotesi
 * porta anche ciò che il capitolo 39 ha letto e svolto.
 *
 * Negli alberi i valori degli indici vanno sempre da 1 a dimension; origin
 * è il numero da cui cominciano nell'enunciato, 0 o 1 (37d): un valore v
 * degli alberi vi è scritto v + origin - 1. label[index_slot(c)] è come
 * l'enunciato scrive l'indice che gli alberi chiamano c: la lettera stessa,
 * o il comando della lettera greca che c rappresenta (37f). */
typedef struct {
    IndexNode *left, *right;
    int dimension;
    int origin;
    IndexSet free;
    int rank[INDEX_LETTERS];
    char label[INDEX_LETTERS][12];

    /* 39d. Le componenti dei tensori che un'ipotesi dà con una tabella o
     * con un elenco: given[index_slot(c)] è NULL se c non è uno di loro,
     * altrimenti punta ai suoi dimension elevato a rank elementi, nell'arena,
     * con il primo indice che varia per ultimo (per righe, in una tabella).
     * Ogni elemento è un albero senza lettere tra gli indici e senza tensori
     * dati: un polinomio nelle componenti dei tensori qualsiasi. */
    IndexNode **given[INDEX_LETTERS];

    /* Solo con una metrica dichiarata (capitolo 39); altrimenti metric è
     * NULL e gli altri campi non contano. left e right sono allora
     * l'identità svolta, senza più indici in alto e in basso, e
     * written_left e written_right quella scritta. */
    IndexNode *written_left, *written_right;
    const Frac *metric;         /* i dimension numeri c_i della diagonale di g_{ij}, tutti diversi da zero;
                                   se metric_top non è NULL dice solo che una metrica c'è */
    IndexNode **metric_top;     /* 39f. Se un elemento della diagonale è una funzione delle coordinate: per ogni
                                   elemento di g_{ij} l'albero del numeratore e, in metric_bottom, quello del
                                   denominatore, fatti di numeri e di lettere senza indici; altrimenti NULL */
    IndexNode **metric_bottom;
    Frac epsilon;               /* quanto vale \varepsilon con gli indici 1, 2, ..., d in ordine, se un'ipotesi
                                   lo dichiara: c'è sempre quando \varepsilon compare nell'identità */
    int epsilon_upper;          /* 1 se quel valore è dichiarato con gli indici in alto */
    const unsigned char *reference[INDEX_LETTERS];  /* per ogni lettera di tensore, dove stanno i suoi
                                                       indici nella prima occorrenza (1 = in alto), o NULL */
} IndexStatement;

extern IndexNode *index_first[INDEX_LETTERS];
int index_is_leaf(const IndexNode *node);
int parse_index_statement(const char *formula, IndexStatement *out);
int parse_index_values(const char *text, int dimension, int origin, IndexStatement *out);
int parse_index_hypotheses(const char *formula, IndexStatement *out);

#endif /* QUAERENS_PARSER_H */
