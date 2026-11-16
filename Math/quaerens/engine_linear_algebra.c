/* MODULO engine_linear_algebra: algebra lineare esatta: matrici, determinanti,
 * sistemi lineari (capitoli 32-33).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in
 * engine_linear_algebra.h, e il resto è static. */
#include "engine_linear_algebra.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"
#include "engine_sign_tables.h"
#include "engine_quantifiers_verdict.h"
#include "engine_sequences.h"
#include "engine_integrals.h"

/* =============================================================================
 * 32. ALGEBRA LINEARE ESATTA: MATRICI A ELEMENTI RAZIONALI
 * ============================================================================
 *
 * Decide gli enunciati del capitolo 31 (parser.c): due espressioni tra
 * matrici scritte per esteso, messe in relazione. "Il prodotto di queste due
 * matrici è quest'altra", "il determinante vale -2", "il rango è 2",
 * "l'inversa è questa". Senza relazione l'enunciato è una richiesta, e la
 * risposta è il valore dell'espressione.
 *
 * COME
 *
 * Un enunciato così non ha lettere: i suoi due membri sono numeri razionali
 * o tabelle di numeri razionali, e si calcolano. Il metodo è uno solo, quello
 * dei libri:
 *
 *   32a. le operazioni tra matrici, con i razionali esatti del capitolo 3;
 *   32b. l'eliminazione di Gauss, che dà il rango, il determinante e
 *        l'inversa, ognuno con un testimone che lo fa ricontrollare
 *        moltiplicando;
 *   32c. i numeri scritti nell'enunciato;
 *   32d. il valore di un'espressione, con le regole sui tipi (un numero o
 *        una matrice) e sulle dimensioni, e la dimensione di I quando non è
 *        scritta;
 *   32e. il confronto dei due membri;
 *   32f. il certificato per checker.c;
 *   32g. una lettera negli elementi: il determinante diventa un polinomio,
 *        trovato con lo stesso conto sui numeri fatto in abbastanza punti,
 *        e l'enunciato con il polinomio al suo posto passa ai capitoli che
 *        sanno deciderlo;
 *   32h. il verdetto, e la risposta di una richiesta, riletta.
 *
 * Nessun numero in virgola mobile: un determinante che vale zero deve valere
 * zero. Nessuna formula per un tipo di matrice: una 2 x 2 e una 5 x 5
 * passano per la stessa eliminazione.
 *
 * CHE COSA VUOL DIRE UN ENUNCIATO
 *
 *   - Due matrici sono uguali se hanno le stesse dimensioni e gli stessi
 *     elementi. Due matrici di dimensioni diverse sono diverse: "=" è falso
 *     e "\neq" è vero.
 *   - Un numero e una matrice sono cose diverse, anche se la matrice è
 *     1 x 1: sommarli o confrontarli è un errore di scrittura, e il verdetto
 *     è NON SUPPORTATO. Fa eccezione lo 0 scritto da solo come membro, che
 *     accanto a una matrice è la matrice nulla delle stesse dimensioni:
 *     "A B = 0", come in ogni libro.
 *   - Un'operazione che non è definita (una somma o un prodotto con le
 *     dimensioni sbagliate, il determinante di una matrice non quadrata,
 *     l'inversa di una matrice singolare) rende l'enunciato senza senso: NON
 *     SUPPORTATO, con il motivo, come \frac{1}{0} = 1 nel capitolo 13. Mai
 *     FALSO: "A^{-1} = B" con A singolare non è un'uguaglianza sbagliata, è
 *     un'uguaglianza che non dice nulla.
 *   - Il rango è la dimensione dello spazio generato dalle righe, sui
 *     razionali; sui reali è lo stesso numero, perché l'eliminazione usa solo
 *     le quattro operazioni.
 *   - x^0 vale 1 per ogni numero x, e A^0 è l'identità per ogni matrice
 *     quadrata A: il prodotto di nessun fattore, come in rat_pow_int().
 *
 * IL CONTROLLO INDIPENDENTE
 *
 * Ha due livelli, e nessuno dei due rifà l'eliminazione.
 *
 * Qui: ogni cosa che l'eliminazione trova (un'inversa, un determinante, un
 * rango) esce con un testimone, e il testimone si ricontrolla con dei
 * prodotti prima di usare il risultato (32b). Moltiplicare è un altro conto
 * rispetto a eliminare: un errore nella ricerca di un perno o in uno
 * scambio fa fallire il prodotto.
 *
 * Nel verificatore: ogni verdetto DIMOSTRATO, FALSO o RISOLTO di questo
 * capitolo vuole che checker.c abbia accettato il certificato (32f), che
 * porta l'enunciato e gli stessi testimoni. Lì i due membri si ricalcolano
 * da capo con un'altra aritmetica (interi a 128 bit invece di 64) e con
 * sole somme, prodotti e confronti: il verificatore non elimina, non cerca
 * perni, non sceglie nulla. Se respinge, il motore ha sbagliato e il
 * verdetto è NON DIMOSTRATO; se non sa controllare (numeri troppo grandi)
 * il verdetto è ancora NON DIMOSTRATO, perché un risultato che il
 * verificatore non ha visto qui non ha un altro controllo che lo regga.
 *
 * PERCHÉ COSÌ
 *
 * Trovare è difficile, controllare è facile: un'eliminazione ha scelte
 * (quale perno, quale scambio) e casi (la colonna senza perno), un prodotto
 * no. Tenere l'eliminazione solo nel motore, e far viaggiare ciò che basta
 * a ricontrollarla, lascia al verificatore il conto più corto da credere.
 * L'alternativa, che il verificatore rifacesse l'eliminazione con il suo
 * codice, è stata la prima versione: due eliminazioni sono lo stesso metodo
 * scritto due volte, e un'idea sbagliata sul metodo sarebbe stata in tutte
 * e due.
 *
 * L'eliminazione sui razionali è la più semplice che dia tutti e tre i
 * testimoni. Quella senza frazioni di Bareiss (18t-h2) tiene i numeri più
 * piccoli, ma dà solo il determinante: qui i numeri sono quelli degli
 * esercizi, e la semplicità vale di più. Un numero che esce dai limiti del
 * capitolo 3 ferma il conto con NON SUPPORTATO.
 *
 * Che cosa manca, e dove andrebbe: con una lettera qui ci sono solo il
 * determinante e la traccia (32g). Il rango con una lettera, confrontato con
 * un numero, si discute per casi nel capitolo 33 (33h), che tratta anche i
 * sistemi lineari e usa l'eliminazione di qui. L'inversa e i confronti tra
 * matrici con una lettera non ci sono ancora: la prima andrebbe in 33h, con
 * il testimone che il verificatore ha già (17d); i secondi vogliono elementi
 * che siano polinomi. I sottospazi (basi, dimensioni, somme e intersezioni)
 * non ci sono ancora, e andrebbero nel capitolo 33.
 */

#define MATRIX_WORK 20000000  /* prodotti tra razionali concessi al conto di un enunciato: un'identità I_{3000}
                                 è una riga di testo, e il suo determinante ne chiederebbe miliardi */

/* Una matrice di numeri razionali: rows righe e cols colonne, almeno una, con
 * gli elementi per righe in at[], nell'arena. L'elemento della riga i e
 * della colonna j, contate da zero, è at[i * cols + j] (matrix_at()). Una
 * matrice con rows e cols a zero è il risultato di un conto fallito: non ha
 * elementi, e ogni ciclo su di lei non fa nulla. */
typedef struct {
    int rows, cols;
    Frac *at;
} Matrix;

/* Il valore di un'espressione del capitolo 31: un numero (is_matrix a 0, in
 * number) oppure una matrice (is_matrix a 1, in matrix). Il campo che non
 * serve non ha significato. */
typedef struct {
    int is_matrix;
    Frac number;
    Matrix matrix;
} MatrixValue;

/* Il valore di un conto fallito: `failure` dice perché. */
static const MatrixValue MATRIX_NONE = {0, {0, 1}, {0, 0, NULL}};

/* I motivi che ricorrono in più punti, e come si dice nel verdetto il metodo
 * di questo capitolo. */
static const char *const MATRIX_SINGULAR = "l'inversa non esiste: la matrice è singolare, cioè il suo determinante è zero";
static const char *const MATRIX_NOT_SQUARE = "determinante, traccia, inversa e potenze sono definiti solo per una matrice quadrata";
static const char *const MATRIX_METHOD = "con il calcolo esatto sulle matrici";

/* Prodotti tra razionali già contati per l'enunciato in corso. */
static _Thread_local long long matrix_work;

/* Conta amount prodotti tra razionali. Ritorna 1 se il conto sta ancora nel
 * suo budget; altrimenti annota l'errore e ritorna 0. */
static int matrix_spend(long long amount) {
    if (amount > MATRIX_WORK - matrix_work) { fail("conto sulle matrici troppo lungo"); return 0; }
    matrix_work += amount;
    return 1;
}

/* 32a. LE OPERAZIONI
 *
 * Ogni funzione ritorna una matrice nuova, nell'arena; dopo un errore
 * ritorna la matrice senza elementi, e chi chiama guarda `failure` alla
 * fine, come nel resto del programma. */

/* Ritorna una matrice rows x cols con gli elementi non inizializzati. Le
 * due dimensioni sono almeno 1: una tabella letta ha almeno un elemento,
 * un'identità un pedice positivo, e le operazioni partono da quelle. */
static Matrix matrix_new(int rows, int cols) {
    Matrix m = {0, 0, NULL};
    if (failure) return m;
    if ((size_t)rows > ARENA_BYTES / sizeof(Frac) / (size_t)cols) { fail(OUT_OF_MEMORY); return m; }
    m.at = arena_alloc((size_t)rows * (size_t)cols * sizeof(Frac));
    if (!m.at) return m;
    m.rows = rows;
    m.cols = cols;
    return m;
}

/* Ritorna l'indirizzo dell'elemento di m nella riga i e colonna j, da zero. */
static Frac *matrix_at(Matrix m, int i, int j) { return &m.at[(size_t)i * (size_t)m.cols + (size_t)j]; }

/* Ritorna la matrice nulla rows x cols. */
static Matrix matrix_zero(int rows, int cols) {
    Matrix m = matrix_new(rows, cols);
    for (int i = 0; i < m.rows * m.cols; i++) m.at[i] = frac_int(0);
    return m;
}

/* Ritorna l'identità n x n: 1 sulla diagonale, 0 altrove. */
static Matrix matrix_identity(int n) {
    Matrix m = matrix_zero(n, n);
    for (int i = 0; i < m.rows; i++) *matrix_at(m, i, i) = frac_int(1);
    return m;
}

/* Ritorna c m: ogni elemento di m moltiplicato per c. */
static Matrix matrix_scale(Matrix m, Frac c) {
    Matrix r = matrix_new(m.rows, m.cols);
    if (!matrix_spend((long long)r.rows * r.cols)) return (Matrix){0, 0, NULL};
    for (int i = 0; i < r.rows * r.cols; i++) r.at[i] = frac_mul(c, m.at[i]);
    return r;
}

/* Ritorna a + b, oppure a - b se subtract è diverso da zero. Le due matrici
 * devono avere le stesse dimensioni: lo controlla chi chiama. */
static Matrix matrix_add(Matrix a, Matrix b, int subtract) {
    Matrix r = matrix_new(a.rows, a.cols);
    for (int i = 0; i < r.rows * r.cols; i++) r.at[i] = frac_add(a.at[i], subtract ? frac_neg(b.at[i]) : b.at[i]);
    return r;
}

/* Ritorna il prodotto righe per colonne a b: l'elemento (i, j) è la somma
 * su k di a(i, k) b(k, j). Le colonne di a devono essere quante le righe di
 * b: lo controlla chi chiama. */
static Matrix matrix_mul(Matrix a, Matrix b) {
    Matrix r = matrix_new(a.rows, b.cols);
    if (!matrix_spend((long long)r.rows * r.cols * a.cols)) return (Matrix){0, 0, NULL};
    for (int i = 0; i < r.rows; i++)
        for (int j = 0; j < r.cols; j++) {
            Frac sum = frac_int(0);
            for (int k = 0; k < a.cols; k++) sum = frac_add(sum, frac_mul(*matrix_at(a, i, k), *matrix_at(b, k, j)));
            *matrix_at(r, i, j) = sum;
        }
    return r;
}

/* Ritorna la trasposta di m: le righe al posto delle colonne. */
static Matrix matrix_transpose(Matrix m) {
    Matrix r = matrix_new(m.cols, m.rows);
    for (int i = 0; i < r.rows; i++)
        for (int j = 0; j < r.cols; j++) *matrix_at(r, i, j) = *matrix_at(m, j, i);
    return r;
}

/* Ritorna 1 se a e b hanno le stesse dimensioni e gli stessi elementi. Se
 * hanno le stesse dimensioni e differiscono, mette in *row e *col il primo
 * posto, da zero, in cui differiscono. */
static int matrix_same(Matrix a, Matrix b, int *row, int *col) {
    if (a.rows != b.rows || a.cols != b.cols) return 0;
    for (int i = 0; i < a.rows; i++)
        for (int j = 0; j < a.cols; j++)
            if (frac_cmp(*matrix_at(a, i, j), *matrix_at(b, i, j)) != 0) { *row = i; *col = j; return 0; }
    return 1;
}

/* 32b. L'ELIMINAZIONE, E I TESTIMONI CHE LASCIA
 *
 * Rango, determinante e inversa vengono tutti dall'eliminazione di Gauss.
 * Ma ciò che il capitolo consegna non è "l'eliminazione ha detto": è un
 * testimone, cioè delle matrici con cui chiunque ricontrolla il risultato
 * moltiplicando, senza rifare l'eliminazione. È ciò che riceve il
 * verificatore (32f), che di eliminazioni non ne fa; e ogni testimone viene
 * ricontrollato già qui, con gli stessi prodotti, prima di essere usato. Un
 * testimone che non torna è un errore dell'eliminazione: conta tra i passi
 * non giustificati, e il conto fallisce.
 *
 * LA FORMA RIDOTTA. Tre operazioni sulle righe di una matrice non cambiano
 * lo spazio che le righe generano: scambiare due righe, moltiplicare una
 * riga per un numero diverso da zero, sommare a una riga un multiplo di
 * un'altra. Con queste si porta la matrice alla forma ridotta: in ogni riga
 * non nulla il primo elemento non nullo, il perno, vale 1; nella colonna di
 * un perno tutti gli altri elementi sono zero; i perni scendono verso
 * destra. Si procede una colonna alla volta:
 *
 *   (1) si cerca, dalla prima riga senza perno in giù, una riga con un
 *       elemento non nullo nella colonna; se non c'è, la colonna non ha
 *       perno e si passa alla successiva;
 *   (2) la si porta al posto della prima riga senza perno, con uno scambio;
 *   (3) la si divide per il suo elemento nella colonna, che diventa 1;
 *   (4) a ogni altra riga si sottrae il multiplo di questa che azzera il
 *       suo elemento nella colonna.
 *
 * Nelle righe sotto i perni già trovati le colonne precedenti sono tutte
 * nulle: quelle con un perno perché (4) le ha azzerate, quelle senza perché
 * lo erano quando sono state saltate, e i passi successivi toccano solo le
 * colonne dalla loro in poi. Per questo (3) e (4) partono dalla colonna del
 * perno.
 *
 * Ogni operazione sulle righe è il prodotto a sinistra per una matrice
 * invertibile. Fatte sulla matrice [A | I], con l'identità accanto, le
 * stesse operazioni lasciano a destra il loro prodotto E: la matrice per cui
 * E A è la forma ridotta di A. Da E vengono i testimoni dell'inversa e del
 * rango. */

/* Porta m alla forma ridotta rispetto alle sue prime `leading` colonne; le
 * altre seguono le stesse operazioni (è il blocco I di [A | I]). m viene
 * modificata. Ritorna il numero dei perni. */
static int matrix_reduce(Matrix m, int leading) {
    int pivots = 0;
    if (!matrix_spend((long long)m.rows * m.cols * (m.rows < leading ? m.rows : leading))) return 0;
    for (int c = 0; c < leading && pivots < m.rows && !failure; c++) {
        /* (1) Il perno della colonna c. */
        int p = pivots;
        while (p < m.rows && matrix_at(m, p, c)->num == 0) p++;
        if (p == m.rows) continue;

        /* (2) Lo scambio. */
        for (int j = 0; j < m.cols && p != pivots; j++) {
            Frac swap = *matrix_at(m, p, j);
            *matrix_at(m, p, j) = *matrix_at(m, pivots, j);
            *matrix_at(m, pivots, j) = swap;
        }

        /* (3) La riga del perno divisa per il perno. */
        Frac pivot = *matrix_at(m, pivots, c);
        for (int j = c; j < m.cols; j++) *matrix_at(m, pivots, j) = frac_div(*matrix_at(m, pivots, j), pivot);

        /* (4) Le altre righe, azzerate nella colonna c. */
        for (int i = 0; i < m.rows; i++) {
            Frac factor = *matrix_at(m, i, c);
            if (i == pivots || factor.num == 0) continue;
            for (int j = c; j < m.cols; j++)
                *matrix_at(m, i, j) = frac_add(*matrix_at(m, i, j), frac_neg(frac_mul(factor, *matrix_at(m, pivots, j))));
        }
        pivots++;
    }
    return pivots;
}

/* Ritorna la matrice [a | I]: a con accanto l'identità che ha le sue righe. */
static Matrix matrix_beside_identity(Matrix a) {
    Matrix both = matrix_new(a.rows, a.cols + a.rows);
    for (int i = 0; i < both.rows; i++)
        for (int j = 0; j < both.cols; j++) *matrix_at(both, i, j) = j < a.cols ? *matrix_at(a, i, j) : frac_int(j - a.cols == i);
    return both;
}

/* Annota che un testimone non ha superato il suo controllo: un errore
 * dell'eliminazione, che ferma il conto. */
static void matrix_witness_failed(void) {
    if (failure) return;
    unjustified_steps++;
    fail("un testimone trovato dall'eliminazione non supera il controllo con i prodotti");
}

/* L'INVERSA. Se A, quadrata di n righe, ha n perni, [A | I] diventa
 * [I | W]: il prodotto E delle operazioni porta A in I, cioè E A = I, e I
 * in W = E. Il testimone è W, e il controllo è A W = I. Per una matrice
 * quadrata basta questo lato: da A W = I segue det(A) det(W) = 1 (teorema di
 * Binet), quindi A è invertibile, e moltiplicando a sinistra per la sua
 * inversa si ottiene che è W. Con meno di n perni una riga di A è
 * combinazione delle altre, e l'inversa non c'è. */

/* Se la matrice quadrata a è invertibile mette in *inverse la sua inversa,
 * ricontrollata, e ritorna 1; altrimenti ritorna 0. */
static int matrix_inverse(Matrix a, Matrix *inverse) {
    int n = a.rows, row, col;
    Matrix both = matrix_beside_identity(a);
    if (matrix_reduce(both, n) != n || failure) return 0;

    /* [I | W]: il blocco di destra. */
    Matrix w = matrix_new(n, n);
    for (int i = 0; i < w.rows; i++)
        for (int j = 0; j < w.cols; j++) *matrix_at(w, i, j) = *matrix_at(both, i, n + j);
    if (!matrix_same(matrix_mul(a, w), matrix_identity(n), &row, &col)) matrix_witness_failed();
    *inverse = w;
    return !failure;
}

/* IL RANGO. È la dimensione dello spazio generato dalle righe, e la forma
 * ridotta la mostra: le righe con un perno sono indipendenti (ognuna ha un 1
 * dove tutte le altre hanno 0), le altre sono nulle, e lo spazio è lo stesso
 * di partenza. Il rango r è quindi il numero dei perni. Il testimone lo
 * fissa da sopra e da sotto con quattro matrici, tutte lette da [A | I]
 * ridotta, dove A ha m righe e n colonne e i perni stanno nelle colonne
 * c_1 < ... < c_r:
 *
 *     F, r righe e n colonne: le righe non nulle della forma ridotta;
 *     C, m righe e r colonne: le colonne c_1, ..., c_r di A;
 *     G, r righe e m colonne: le prime r righe di E;
 *     H, n righe e r colonne: 1 nel posto (c_i, i), 0 altrove.
 *
 *   A = C F. La colonna j della forma ridotta dice come la colonna j di A
 *   si scrive con le colonne dei perni: le operazioni sulle righe non
 *   cambiano le relazioni tra le colonne. Le righe di A sono allora
 *   combinazioni delle r righe di F: il rango è al più r.
 *
 *   G A H = I. G A sono le prime r righe di E A, cioè F; e F H prende di F
 *   le colonne dei perni, che sono l'identità. Le r righe di G A sono quindi
 *   indipendenti (una loro combinazione nulla, moltiplicata per H, dà i
 *   coefficienti stessi) e sono combinazioni delle righe di A: il rango è
 *   almeno r.
 *
 * Con r = 0 la matrice è nulla, e non c'è nulla da moltiplicare. */

/* Il testimone del rango di una matrice (vedi qui sopra). Con rank = 0 le
 * quattro matrici non hanno elementi. */
typedef struct {
    int rank;        /* il rango r */
    Matrix c, f;     /* A = C F: il rango è al più r */
    Matrix g, h;     /* G A H = I: il rango è almeno r */
} RankWitness;

/* Ritorna il rango di a con il suo testimone, ricontrollato. */
static RankWitness matrix_rank(Matrix a) {
    RankWitness w = {0, {0, 0, NULL}, {0, 0, NULL}, {0, 0, NULL}, {0, 0, NULL}};
    int m = a.rows, n = a.cols, row, col;
    Matrix both = matrix_beside_identity(a);
    int r = matrix_reduce(both, n);
    if (failure || r == 0) return w;

    /* Le quattro matrici. La colonna del perno della riga i è la prima in
     * cui la riga ridotta non è zero. */
    w.c = matrix_new(m, r);
    w.f = matrix_new(r, n);
    w.g = matrix_new(r, m);
    w.h = matrix_zero(n, r);
    if (failure) return w;
    for (int i = 0; i < r; i++) {
        int pivot = 0;
        while (matrix_at(both, i, pivot)->num == 0) pivot++;
        for (int j = 0; j < n; j++) *matrix_at(w.f, i, j) = *matrix_at(both, i, j);
        for (int j = 0; j < m; j++) *matrix_at(w.g, i, j) = *matrix_at(both, i, n + j);
        for (int k = 0; k < m; k++) *matrix_at(w.c, k, i) = *matrix_at(a, k, pivot);
        *matrix_at(w.h, pivot, i) = frac_int(1);
    }

    /* I due controlli, con soli prodotti. */
    if (!matrix_same(matrix_mul(w.c, w.f), a, &row, &col) ||
        !matrix_same(matrix_mul(matrix_mul(w.g, a), w.h), matrix_identity(r), &row, &col)) matrix_witness_failed();
    w.rank = r;
    return w;
}

/* IL DETERMINANTE. Qui l'eliminazione è quella che non divide le righe e
 * non tocca quelle sopra il perno, perché di ogni passo resti traccia: per
 * ogni colonna k,
 *
 *   (1) si cerca dalla riga k in giù un elemento non nullo nella colonna, e
 *       lo si porta nella riga k con uno scambio; se non c'è, la colonna è
 *       già a posto e si passa oltre;
 *   (2) a ogni riga i sotto la k si sottrae la riga k moltiplicata per
 *       f = (elemento di i nella colonna) / (perno), e f si annota.
 *
 * Alla fine la matrice è U, triangolare superiore. Gli f annotati, messi
 * sotto la diagonale di una matrice L che ha 1 sulla diagonale, e l'ordine
 * p in cui gli scambi hanno lasciato le righe di A, danno
 *
 *     (la matrice che ha per riga i la riga p_i di A) = L U:
 *
 * disfare i passi (2), dal primo all'ultimo, vuol dire sommare alla riga i
 * la riga k per f, ed è ciò che fa il prodotto per L. Uno scambio fatto al
 * passo k scambia anche gli f già annotati delle due righe: sono i
 * moltiplicatori di quelle righe, e le seguono.
 *
 * Il determinante cambia segno a ogni scambio e non cambia in (2); quello
 * di una matrice triangolare è il prodotto della diagonale. Quindi
 *
 *     det(A) = (+1 o -1 secondo il numero degli scambi) u_11 u_22 ... u_nn.
 *
 * Il testimone è (p, L, U), e il controllo è l'uguaglianza scritta sopra,
 * un prodotto. Vale anche per una matrice singolare: una colonna senza
 * perno lascia uno zero sulla diagonale di U, e il determinante è zero. */

/* Il testimone del determinante di una matrice quadrata di n righe (vedi qui
 * sopra), con il determinante che se ne legge. */
typedef struct {
    Frac value;   /* il determinante */
    int *row;     /* la permutazione p: n numeri da 1 a n, nell'arena */
    Matrix l, u;  /* L triangolare inferiore con 1 sulla diagonale, U triangolare superiore */
} DeterminantWitness;

/* Ritorna il determinante della matrice quadrata a con il suo testimone,
 * ricontrollato. */
static DeterminantWitness matrix_determinant(Matrix a) {
    DeterminantWitness w = {frac_int(0), NULL, {0, 0, NULL}, {0, 0, NULL}};
    int n = a.rows, row, col;
    w.row = arena_alloc((size_t)n * sizeof *w.row);
    w.l = matrix_identity(n);
    w.u = matrix_new(n, n);
    if (failure || !w.row || !matrix_spend((long long)n * n * n)) return w;
    memcpy(w.u.at, a.at, (size_t)n * (size_t)n * sizeof(Frac));
    for (int i = 0; i < n; i++) w.row[i] = i + 1;
    Frac value = frac_int(1);
    for (int k = 0; k < n && !failure; k++) {
        /* (1) Il perno, e lo scambio: delle righe di U, dei moltiplicatori
         * già annotati in L, dei posti nella permutazione. */
        int p = k;
        while (p < n && matrix_at(w.u, p, k)->num == 0) p++;
        if (p == n) continue;
        if (p != k) {
            for (int j = 0; j < n; j++) {
                Frac swap = *matrix_at(w.u, p, j);
                *matrix_at(w.u, p, j) = *matrix_at(w.u, k, j);
                *matrix_at(w.u, k, j) = swap;
            }
            for (int j = 0; j < k; j++) {
                Frac swap = *matrix_at(w.l, p, j);
                *matrix_at(w.l, p, j) = *matrix_at(w.l, k, j);
                *matrix_at(w.l, k, j) = swap;
            }
            int swap = w.row[p];
            w.row[p] = w.row[k];
            w.row[k] = swap;
            value = frac_neg(value);
        }

        /* (2) Le righe sotto, con il moltiplicatore annotato. */
        for (int i = k + 1; i < n; i++) {
            if (matrix_at(w.u, i, k)->num == 0) continue;
            Frac f = frac_div(*matrix_at(w.u, i, k), *matrix_at(w.u, k, k));
            *matrix_at(w.l, i, k) = f;
            for (int j = k; j < n; j++) *matrix_at(w.u, i, j) = frac_add(*matrix_at(w.u, i, j), frac_neg(frac_mul(f, *matrix_at(w.u, k, j))));
        }
    }
    for (int i = 0; i < n; i++) value = frac_mul(value, *matrix_at(w.u, i, i));

    /* Il controllo: le righe di a nell'ordine p sono L U. */
    Matrix permuted = matrix_new(n, n);
    for (int i = 0; i < permuted.rows; i++)
        for (int j = 0; j < n; j++) *matrix_at(permuted, i, j) = *matrix_at(a, w.row[i] - 1, j);
    if (!matrix_same(matrix_mul(w.l, w.u), permuted, &row, &col)) matrix_witness_failed();
    w.value = value;
    return w;
}

/* 32c. I NUMERI DELL'ENUNCIATO
 *
 * Gli elementi delle tabelle e i fattori numerici arrivano dal capitolo 9
 * come alberi di espressioni. Qui devono essere numeri razionali scritti
 * con le quattro operazioni e le potenze a esponente intero scritto: sono
 * le sole cose che la notazione dei certificati delle matrici sa dire
 * (matrix_cert_number()), e un numero che il verificatore non può
 * ricalcolare non entra in un verdetto di questo capitolo. Una radice, \pi,
 * una funzione fermano il conto con il motivo. Una lettera anche, tranne
 * quando 32g le ha dato un valore: lì il conto si fa in un punto alla volta,
 * e in ogni punto la lettera è un numero. Lo stesso vale per le lettere di
 * un sistema quando il capitolo 33 ne calcola un'equazione in un punto: i
 * loro alberi non entrano mai in un certificato, che del sistema scrive i
 * coefficienti.
 *
 * Warning: matrix_number() e matrix_cert_number() devono accettare gli
 * stessi alberi. Se ne allarghi una, allarga l'altra, il capitolo 17 di
 * checker.c e, per ciò che può contenere una lettera, letter_degree_number()
 * (32g). */

#define MAX_LETTERS 3  /* lettere diverse in un'espressione di 32g */

/* Le lettere a cui 32g ha dato un valore: letter_name[i] vale
 * letter_value[i], per i minore di letter_count. Fuori da 32g letter_count
 * è zero, e una lettera in un enunciato ferma il conto. */
static _Thread_local int letter_name[MAX_LETTERS], letter_count;
static _Thread_local Frac letter_value[MAX_LETTERS];

/* Le lettere di un sistema a cui il capitolo 33 ha dato un valore, per
 * calcolare un'equazione in un punto: la lettera placed_letter[i], con il
 * suo pedice, vale placed_value[i], per i minore di placed_count. Sono le
 * incognite, o i parametri di un insieme scritto: possono avere un pedice e
 * sono più di MAX_LETTERS, per questo hanno un elenco loro. Fuori dal
 * capitolo 33 placed_count è zero. */
static _Thread_local const LinearLetter *placed_letter;
static _Thread_local const Frac *placed_value;
static _Thread_local int placed_count;

/* 1 mentre il capitolo 33 scrive il certificato di un fatto in un valore
 * speciale di un parametro: lì una lettera che ha un valore si scrive come
 * il numero che vale, e il certificato è uno di quelli sui numeri (32f). */
static _Thread_local int letter_numbers;

/* Se node è un esponente intero scritto, un numero o il suo opposto, lo
 * mette in *exponent e ritorna 1. */
static int matrix_exponent_value(const Node *node, long long *exponent) {
    int negative = node->kind == N_NEG;
    if (negative) node = node->a;
    if (node->kind != N_NUM) return 0;
    *exponent = negative ? -node->value : node->value;
    return 1;
}

/* Ritorna base elevato a exponent, anche negativo, con le moltiplicazioni
 * ripetute di rat_pow_int(). */
static Frac matrix_number_power(Frac base, long long exponent) {
    if (exponent < -MAX_POWER || exponent > MAX_POWER) { fail("esponente costante troppo grande"); return frac_int(0); }
    if (exponent < 0) { base = frac_div(frac_int(1), base); exponent = -exponent; }
    Frac result = frac_int(1);
    for (long long i = 0; i < exponent && !failure; i++) result = frac_mul(result, base);
    return result;
}

/* Ritorna il numero razionale scritto dall'albero node. */
static Frac matrix_number(const Node *node) {
    long long exponent;
    if (failure) return frac_int(0);
    switch (node->kind) {
    case N_NUM: return frac_make(node->value, 1);
    case N_VAR:
        for (int i = 0; i < placed_count; i++)
            if (placed_letter[i].name == node->name && placed_letter[i].index == -1) return placed_value[i];
        for (int i = 0; i < letter_count; i++)
            if (letter_name[i] == node->name) return letter_value[i];
        break;
    case N_SEQ:
        /* Una lettera con il pedice numerico, x_{1}: solo tra quelle di un
         * sistema. */
        for (int i = 0; i < placed_count && node->a->kind == N_NUM; i++)
            if (placed_letter[i].name == node->name && placed_letter[i].index == node->a->value) return placed_value[i];
        break;
    case N_NEG: return frac_neg(matrix_number(node->a));
    case N_ADD: return frac_add(matrix_number(node->a), matrix_number(node->b));
    case N_SUB: return frac_add(matrix_number(node->a), frac_neg(matrix_number(node->b)));
    case N_MUL: return frac_mul(matrix_number(node->a), matrix_number(node->b));
    case N_DIV: return frac_div(matrix_number(node->a), matrix_number(node->b));
    case N_POW:
        if (matrix_exponent_value(node->b, &exponent)) return matrix_number_power(matrix_number(node->a), exponent);
        break;
    default:
        break;
    }
    fail("in un enunciato sulle matrici i numeri si scrivono con interi, frazioni, somme, prodotti e potenze intere: "
         "niente radici o funzioni, e una lettera solo se l'enunciato dice dove sta, con \\forall k \\in \\mathbb{R} o \\{k \\in \\mathbb{R} \\mid ...\\}");
    return frac_int(0);
}

/* 32d. IL VALORE DI UN'ESPRESSIONE
 *
 * Ogni nodo vale un numero o una matrice, e ogni operazione dice che cosa
 * accetta:
 *
 *     -a, a + b, a - b   due numeri, o due matrici con le stesse dimensioni;
 *     a b                due numeri; un numero e una matrice (il multiplo);
 *                        due matrici, con le colonne di a quante le righe di b;
 *     a^k                un numero, o una matrice quadrata; con k negativo
 *                        l'inverso, o l'inversa, elevati a -k;
 *     a^T                una matrice;
 *     det, tr            una matrice quadrata;       rango: una matrice.
 *
 * Ogni altra combinazione ferma il conto con il suo motivo: l'enunciato non
 * ha senso così com'è scritto.
 *
 * LA DIMENSIONE DI I. Nei libri l'identità si scrive quasi sempre senza
 * pedice: "A^2 - 5A + 6I = 0", "A B = I". La sua dimensione è quella che
 * rende sensata l'operazione in cui compare, e c'è un solo modo di
 * sceglierla:
 *
 *   - sommata a una matrice, o confrontata con una matrice: il numero delle
 *     sue righe;
 *   - moltiplicata a destra di una matrice, A I: il numero delle colonne
 *     di A; a sinistra, I A: il numero delle righe;
 *   - dentro un opposto, una trasposta, una potenza, un multiplo: quella
 *     che il contesto chiede a tutta l'espressione.
 *
 * Per questo il valore si calcola portando con sé `want`, la dimensione
 * che il contesto chiede a un'identità senza pedice (0 se non ne chiede
 * nessuna), e di due operandi si calcola prima quello che la sua dimensione
 * la sa già (matrix_shape()), per ricavarne quella dell'altro. Dove nessun
 * contesto la fissa, "\det I" o "I = I", il conto si ferma: va scritta.
 * Trovata, la dimensione resta annotata nel nodo, così il certificato scrive
 * un'identità con la sua dimensione, e il verificatore non deve dedurre
 * nulla.
 *
 * Se la matrice accanto non è quadrata, la dimensione presa è quella che
 * rende l'identità diversa da lei: "A B = I" con A B di 2 righe e 3 colonne
 * è falso qualunque sia I, e "A + I" non è definita. */

/* Che cosa si sa della forma di un'espressione senza calcolarla, in ordine
 * crescente: è un numero; è fatta solo di identità senza dimensione; ha una
 * matrice con le dimensioni scritte. */
enum { SHAPE_NUMBER, SHAPE_OPEN, SHAPE_FIXED };

/* Il vettore incognito di un sistema scritto A x = B (capitolo 33): mentre
 * vector_name non è zero, la lettera con quel nome scritta da sola non è un
 * numero ma la colonna vector_value. Fuori dal capitolo 33 vector_name è
 * zero. */
static _Thread_local int vector_name;
static _Thread_local Matrix vector_value;

/* Ritorna 1 se node è il vettore incognito scritto da solo. */
static int matrix_is_vector(const MatrixNode *node) {
    return vector_name && node->kind == M_SCALAR && node->scalar->kind == N_VAR && node->scalar->name == vector_name;
}

/* Ritorna la forma, tra le tre qui sopra, dell'espressione node. */
static int matrix_shape(const MatrixNode *node) {
    switch (node->kind) {
    case M_SCALAR:
        return matrix_is_vector(node) ? SHAPE_FIXED : SHAPE_NUMBER;
    case M_DET: case M_RANK: case M_TRACE:
        return SHAPE_NUMBER;
    case M_TABLE:
        return SHAPE_FIXED;
    case M_IDENTITY:
        return node->rows ? SHAPE_FIXED : SHAPE_OPEN;
    case M_NEG: case M_POWER: case M_TRANSPOSE:
        return matrix_shape(node->a);
    default: {
        int a = matrix_shape(node->a), b = matrix_shape(node->b);
        return a > b ? a : b;
    }
    }
}

/* Ritorna la dimensione che un'identità senza pedice deve avere accanto al
 * valore first, già calcolato, in un'operazione di tipo kind (M_MUL per il
 * prodotto; ogni altro tipo vale per la somma e per il confronto).
 * first_is_left dice se first è l'operando di sinistra; want è la
 * dimensione che il contesto chiede all'operazione intera, e passa oltre un
 * numero: in 2 I la dimensione di I non la dà il 2. */
static int matrix_want(MatrixKind kind, MatrixValue first, int first_is_left, int want) {
    if (!first.is_matrix) return want;
    return kind == M_MUL && first_is_left ? first.matrix.cols : first.matrix.rows;
}

/* Ritorna value elevato a power (vedi la tabella in testa al paragrafo). */
static MatrixValue matrix_power(MatrixValue value, long long power) {
    if (failure) return MATRIX_NONE;
    if (!value.is_matrix) return (MatrixValue){0, matrix_number_power(value.number, power), {0, 0, NULL}};
    if (power < -MAX_POWER || power > MAX_POWER) { fail("esponente costante troppo grande"); return MATRIX_NONE; }
    if (value.matrix.rows != value.matrix.cols) { fail(MATRIX_NOT_SQUARE); return MATRIX_NONE; }
    Matrix base = value.matrix;
    if (power < 0 && !matrix_inverse(value.matrix, &base)) { fail(MATRIX_SINGULAR); return MATRIX_NONE; }
    Matrix result = matrix_identity(base.rows);
    for (long long i = 0; i < (power < 0 ? -power : power) && !failure; i++) result = matrix_mul(result, base);
    return (MatrixValue){1, {0, 1}, result};
}

/* Ritorna il risultato dell'operazione kind (M_ADD, M_SUB o M_MUL) tra i
 * valori x e y, nell'ordine in cui sono scritti. */
static MatrixValue matrix_combine(MatrixKind kind, MatrixValue x, MatrixValue y) {
    if (failure) return MATRIX_NONE;
    if (kind == M_MUL) {
        if (!x.is_matrix && !y.is_matrix) return (MatrixValue){0, frac_mul(x.number, y.number), {0, 0, NULL}};
        if (!x.is_matrix) return (MatrixValue){1, {0, 1}, matrix_scale(y.matrix, x.number)};
        if (!y.is_matrix) return (MatrixValue){1, {0, 1}, matrix_scale(x.matrix, y.number)};
        if (x.matrix.cols != y.matrix.rows) { fail("prodotto di due matrici non definito: le colonne della prima non sono quante le righe della seconda"); return MATRIX_NONE; }
        return (MatrixValue){1, {0, 1}, matrix_mul(x.matrix, y.matrix)};
    }
    if (x.is_matrix != y.is_matrix) { fail("un numero e una matrice non si sommano"); return MATRIX_NONE; }
    if (!x.is_matrix) return (MatrixValue){0, frac_add(x.number, kind == M_SUB ? frac_neg(y.number) : y.number), {0, 0, NULL}};
    if (x.matrix.rows != y.matrix.rows || x.matrix.cols != y.matrix.cols) { fail("somma di due matrici non definita: non hanno le stesse dimensioni"); return MATRIX_NONE; }
    return (MatrixValue){1, {0, 1}, matrix_add(x.matrix, y.matrix, kind == M_SUB)};
}

/* Ritorna il valore dell'espressione node, con want la dimensione chiesta
 * dal contesto a un'identità senza pedice (0 se non ne chiede). Annota nel
 * nodo di ogni identità senza pedice la dimensione trovata. Dopo un errore
 * `failure` dice perché, e il valore non ha significato. */
static MatrixValue matrix_eval(MatrixNode *node, int want) {
    if (failure) return MATRIX_NONE;
    switch (node->kind) {
    case M_SCALAR:
        /* Il vettore incognito di un sistema vale la sua colonna; dentro
         * un'altra espressione, x^{2} o \frac{x}{2}, non è più un numero
         * del capitolo 9, e non si legge. */
        if (matrix_is_vector(node)) return (MatrixValue){1, {0, 1}, vector_value};
        if (vector_name && node_has_variable(node->scalar, vector_name)) {
            fail("il vettore incognito di un sistema va scritto da solo, come in A x = B: non dentro una frazione, una potenza o una funzione");
            return MATRIX_NONE;
        }
        return (MatrixValue){0, matrix_number(node->scalar), {0, 0, NULL}};
    case M_TABLE: {
        Matrix m = matrix_new(node->rows, node->cols);
        for (int i = 0; i < m.rows * m.cols; i++) m.at[i] = matrix_number(node->entry[i]);
        return (MatrixValue){1, {0, 1}, m};
    }
    case M_IDENTITY:
        if (!node->rows && !want) { fail("la dimensione di I non è fissata dal contesto: va scritta con il pedice, I_{n}"); return MATRIX_NONE; }
        if (!node->rows) node->rows = want;
        return (MatrixValue){1, {0, 1}, matrix_identity(node->rows)};
    case M_NEG: {
        MatrixValue a = matrix_eval(node->a, want);
        if (!a.is_matrix) return (MatrixValue){0, frac_neg(a.number), {0, 0, NULL}};
        return (MatrixValue){1, {0, 1}, matrix_scale(a.matrix, frac_int(-1))};
    }
    case M_POWER:
        return matrix_power(matrix_eval(node->a, want), node->power);
    case M_TRANSPOSE: {
        MatrixValue a = matrix_eval(node->a, want);
        if (!failure && !a.is_matrix) fail("la trasposta si fa di una matrice, non di un numero");
        return failure ? MATRIX_NONE : (MatrixValue){1, {0, 1}, matrix_transpose(a.matrix)};
    }
    case M_DET: case M_RANK: case M_TRACE: {
        /* L'argomento è un'espressione a sé: il contesto non gli chiede nulla. */
        MatrixValue a = matrix_eval(node->a, 0);
        Frac trace = frac_int(0);
        if (failure) return MATRIX_NONE;
        if (!a.is_matrix) { fail("determinante, rango e traccia si calcolano di una matrice, non di un numero"); return MATRIX_NONE; }
        if (node->kind != M_RANK && a.matrix.rows != a.matrix.cols) { fail(MATRIX_NOT_SQUARE); return MATRIX_NONE; }
        if (node->kind == M_RANK) return (MatrixValue){0, frac_int(matrix_rank(a.matrix).rank), {0, 0, NULL}};
        if (node->kind == M_DET) return (MatrixValue){0, matrix_determinant(a.matrix).value, {0, 0, NULL}};
        for (int i = 0; i < a.matrix.rows; i++) trace = frac_add(trace, *matrix_at(a.matrix, i, i));
        return (MatrixValue){0, trace, {0, 0, NULL}};
    }
    default: {
        /* Somma, differenza, prodotto: prima l'operando che sa la propria
         * dimensione, poi l'altro con quella che il primo gli impone. */
        MatrixValue x, y;
        if (matrix_shape(node->b) > matrix_shape(node->a)) {
            y = matrix_eval(node->b, want);
            x = matrix_eval(node->a, matrix_want(node->kind, y, 0, want));
        } else {
            x = matrix_eval(node->a, want);
            y = matrix_eval(node->b, matrix_want(node->kind, x, 1, want));
        }
        return matrix_combine(node->kind, x, y);
    }
    }
}

/* 32e. IL CONFRONTO E LA SCRITTURA DEI VALORI */

/* Ritorna 1 se node è lo 0 scritto da solo: accanto a una matrice è la
 * matrice nulla (vedi la testa del capitolo). */
static int matrix_is_zero(const MatrixNode *node) {
    return node->kind == M_SCALAR && node->scalar->kind == N_NUM && node->scalar->value == 0;
}

/* Aggiunge alla dimostrazione in corso il valore value in LaTeX: un numero,
 * oppure la matrice tra parentesi tonde. È scritto in modo che il capitolo
 * 31 lo rilegga uguale: serve anche per la risposta di una richiesta. */
static void matrix_put(MatrixValue value) {
    char number[64];
    if (!value.is_matrix) {
        number[0] = 0;
        frac_latex(value.number, number, sizeof number);
        proof_add("%s", number);
        return;
    }
    proof_add("\\begin{pmatrix} ");
    for (int i = 0; i < value.matrix.rows; i++)
        for (int j = 0; j < value.matrix.cols; j++) {
            number[0] = 0;
            frac_latex(*matrix_at(value.matrix, i, j), number, sizeof number);
            proof_add("%s%s", j ? " & " : i ? " \\\\ " : "", number);
        }
    proof_add(" \\end{pmatrix}");
}

/* Ritorna 1 se tra i valori left e right vale relation, 0 se non vale; in
 * tutti e due i casi scrive in note, di size byte, che cosa lo mostra, in
 * italiano. Tra due matrici si confronta solo con = e \neq; tra un numero e
 * una matrice mai (lo 0 da solo è già diventato la matrice nulla): in
 * quei casi annota l'errore. */
static int matrix_holds(MatrixValue left, MatrixValue right, MatrixRelation relation, char *note, size_t size) {
    char a[64] = "", b[64] = "";
    int row = 0, col = 0;
    note[0] = 0;
    if (failure) return 0;
    if (left.is_matrix != right.is_matrix) { fail("un numero e una matrice non si confrontano: solo lo 0 da solo, che è la matrice nulla"); return 0; }
    if (!left.is_matrix) {
        int order = frac_cmp(left.number, right.number);
        frac_latex(left.number, a, sizeof a);
        frac_latex(right.number, b, sizeof b);
        snprintf(note, size, "il primo membro vale %s, il secondo %s", a, b);
        return relation == MATRIX_EQ ? order == 0 : relation == MATRIX_NEQ ? order != 0 : relation == MATRIX_LT ? order < 0 :
               relation == MATRIX_LE ? order <= 0 : relation == MATRIX_GT ? order > 0 : order >= 0;
    }
    if (relation != MATRIX_EQ && relation != MATRIX_NEQ) { fail("due matrici si confrontano solo con = e \\neq"); return 0; }
    int same = matrix_same(left.matrix, right.matrix, &row, &col);
    if (same) {
        snprintf(note, size, "i due membri sono la stessa matrice");
    } else if (left.matrix.rows != right.matrix.rows || left.matrix.cols != right.matrix.cols) {
        snprintf(note, size, "il primo membro è una matrice %d x %d, il secondo %d x %d", left.matrix.rows, left.matrix.cols,
                 right.matrix.rows, right.matrix.cols);
    } else {
        frac_latex(*matrix_at(left.matrix, row, col), a, sizeof a);
        frac_latex(*matrix_at(right.matrix, row, col), b, sizeof b);
        snprintf(note, size, "nella riga %d e colonna %d il primo membro vale %s, il secondo %s", row + 1, col + 1, a, b);
    }
    return (relation == MATRIX_EQ) == same;
}

/* 32f. IL CERTIFICATO
 *
 * Il certificato è l'enunciato, riscritto nella notazione del capitolo 17
 * di checker.c, con la verità che il motore afferma e un testimone per
 * ogni determinante, rango e inversa:
 *
 *     certificate matrices
 *     statement (= (det (matrix 2 2 1 2 3 4)) -2)
 *     claim true
 *     witness lu 1 2 (matrix 2 2 1 0 3 1) (matrix 2 2 1 2 0 -2)
 *     end
 *
 * Il verificatore non fa eliminazioni: somma, moltiplica e confronta. Ciò
 * che è un conto diretto (somme, prodotti, trasposte, potenze, tracce) lo
 * rifà da sé; ciò che il motore ha trovato eliminando lo ricontrolla sul
 * testimone, che è lo stesso che 32b ha già ricontrollato qui:
 *
 *     witness inverse W            A W è l'identità;
 *     witness lu p1 ... pn L U     le righe di A nell'ordine p sono L U;
 *     witness rank r C F G H       A = C F, e G A H è l'identità;
 *     witness rank 0               A è la matrice nulla.
 *
 * I testimoni stanno dopo l'enunciato, uno per riga, nell'ordine in cui il
 * verificatore li chiede leggendo: per ogni nodo prima quelli dei suoi
 * operandi, da sinistra a destra, poi il suo. È l'ordine in cui
 * matrix_cert_node() scrive, e matrix_cert_witnesses() lo ripercorre
 * uguale.
 *
 * I nomi dati dall'enunciato non ci sono: dove compare un nome è scritta la
 * sua definizione, e i suoi testimoni si ripetono. Che cosa cambia rispetto
 * all'enunciato com'è scritto, ed è tutto ciò che il verificatore non
 * ricontrolla perché è lettura: l'identità ha sempre la sua dimensione
 * (32d), lo 0 accanto a una matrice è scritto (zero r c), > e \ge sono
 * scritti come < e <= con i membri scambiati, una potenza negativa come
 * potenza dell'inversa.
 *
 * Warning: se aggiungi un tipo di nodo o una relazione, aggiungi qui la sua
 * parola e nel capitolo 17 di checker.c il suo conto; se il nodo nuovo
 * vuole un testimone, anche il suo caso in matrix_cert_witnesses(), nello
 * stesso ordine di matrix_cert_node(). */

/* Scrive il numero dell'albero node, uno di quelli che matrix_number()
 * accetta: gli stessi casi, con le parole del verificatore. Una lettera si
 * scrive com'è: serve al certificato di uno sviluppo (32g). */
static void matrix_cert_number(const Node *node) {
    static const char *const words[] = {[N_NEG] = "neg", [N_ADD] = "+", [N_SUB] = "-", [N_MUL] = "*", [N_DIV] = "/"};
    long long exponent;
    switch (node->kind) {
    case N_NUM:
        cert_add("%lld", node->value);
        return;
    case N_VAR:
        if (node->name >= 128 || !islower(node->name)) break;
        for (int i = 0; letter_numbers && i < letter_count; i++)
            if (letter_name[i] == node->name) { cert_frac(letter_value[i]); return; }
        if (letter_numbers) break;
        cert_add("%c", node->name);
        return;
    case N_NEG: case N_ADD: case N_SUB: case N_MUL: case N_DIV:
        cert_add("(%s ", words[node->kind]);
        matrix_cert_number(node->a);
        if (node->b) { cert_add(" "); matrix_cert_number(node->b); }
        cert_add(")");
        return;
    case N_POW:
        /* a^{-k} è 1 / a^k: la potenza del verificatore ha un esponente
         * non negativo. */
        if (!matrix_exponent_value(node->b, &exponent)) break;
        cert_add(exponent < 0 ? "(/ 1 (^ " : "(^ ");
        matrix_cert_number(node->a);
        cert_add(exponent < 0 ? " %lld))" : " %lld)", exponent < 0 ? -exponent : exponent);
        return;
    default:
        break;
    }
    certificate_broken = 1;
}

/* Scrive, preceduta da uno spazio, la matrice di numeri m: (matrix righe
 * colonne elementi...). */
static void matrix_cert_table(Matrix m) {
    cert_add(" (matrix %d %d", m.rows, m.cols);
    for (int i = 0; i < m.rows * m.cols; i++) {
        cert_add(" ");
        cert_frac(m.at[i]);
    }
    cert_add(")");
}

/* Scrive l'espressione node, senza testimoni. Va chiamata dopo
 * matrix_eval(), che ha annotato le dimensioni delle identità: una ancora
 * senza dimensione rende certificate_broken uguale a 1. */
static void matrix_cert_node(MatrixNode *node) {
    static const char *const words[] = {[M_NEG] = "neg", [M_ADD] = "+", [M_SUB] = "-", [M_MUL] = "*",
                                        [M_TRANSPOSE] = "transpose", [M_DET] = "det", [M_RANK] = "rank", [M_TRACE] = "trace"};
    switch (node->kind) {
    case M_SCALAR:
        matrix_cert_number(node->scalar);
        return;
    case M_TABLE:
        cert_add("(matrix %d %d", node->rows, node->cols);
        for (int i = 0; i < node->rows * node->cols; i++) {
            cert_add(" ");
            matrix_cert_number(node->entry[i]);
        }
        cert_add(")");
        return;
    case M_IDENTITY:
        if (!node->rows) certificate_broken = 1;
        cert_add("(identity %d)", node->rows);
        return;
    case M_POWER: {
        /* Con l'esponente negativo: l'inverso di un numero, o l'inversa di
         * una matrice, elevati all'opposto. Che cosa sia la base lo dice la
         * sua forma, ora che le identità hanno la loro dimensione. */
        const char *inverse = node->power >= 0 ? "" : matrix_shape(node->a) == SHAPE_NUMBER ? "(/ 1 " : "(inv ";
        cert_add("(^ %s", inverse);
        matrix_cert_node(node->a);
        cert_add("%s %lld)", inverse[0] ? ")" : "", node->power < 0 ? -node->power : node->power);
        return;
    }
    default:
        cert_add("(%s ", words[node->kind]);
        matrix_cert_node(node->a);
        if (node->b) { cert_add(" "); matrix_cert_node(node->b); }
        cert_add(")");
        return;
    }
}

/* Scrive le voci witness dell'espressione node, una per riga, nell'ordine
 * in cui il verificatore le chiede (vedi la testa del paragrafo). Ogni
 * testimone si ricava ricalcolando il valore dell'operando: è lo stesso
 * conto di matrix_eval(), che lo ha già ricontrollato. Un conto che qui
 * fallisce rende certificate_broken uguale a 1. */
static void matrix_cert_witnesses(MatrixNode *node) {
    /* Prima gli operandi, da sinistra a destra. */
    if (node->a) matrix_cert_witnesses(node->a);
    if (node->b) matrix_cert_witnesses(node->b);
    int inverse = node->kind == M_POWER && node->power < 0 && matrix_shape(node->a) != SHAPE_NUMBER;
    if (node->kind != M_DET && node->kind != M_RANK && !inverse) return;

    /* Poi il nodo: il valore del suo operando, e ciò che l'eliminazione ne
     * lascia. */
    MatrixValue a = matrix_eval(node->a, 0);
    if (failure || !a.is_matrix) { certificate_broken = 1; return; }
    if (inverse) {
        Matrix w;
        if (!matrix_inverse(a.matrix, &w)) { certificate_broken = 1; return; }
        cert_add("witness inverse");
        matrix_cert_table(w);
    } else if (node->kind == M_DET) {
        DeterminantWitness w = matrix_determinant(a.matrix);
        if (failure) { certificate_broken = 1; return; }
        cert_add("witness lu");
        for (int i = 0; i < a.matrix.rows; i++) cert_add(" %d", w.row[i]);
        matrix_cert_table(w.l);
        matrix_cert_table(w.u);
    } else {
        RankWitness w = matrix_rank(a.matrix);
        if (failure) { certificate_broken = 1; return; }
        cert_add("witness rank %d", w.rank);
        if (w.rank) {
            matrix_cert_table(w.c);
            matrix_cert_table(w.f);
            matrix_cert_table(w.g);
            matrix_cert_table(w.h);
        }
    }
    cert_add("\n");
}

/* Scrive in certificate_text il certificato dell'enunciato st, i cui membri
 * valgono left e right, con la verità truth. Un membro che è lo 0 da solo
 * accanto a una matrice si scrive come la matrice nulla che è. */
static void matrix_certificate(const MatrixStatement *st, MatrixValue left, MatrixValue right, int truth) {
    static const char *const words[] = {[MATRIX_EQ] = "=", [MATRIX_NEQ] = "neq", [MATRIX_LT] = "<", [MATRIX_LE] = "<=",
                                        [MATRIX_GT] = "<", [MATRIX_GE] = "<="};
    int swapped = st->relation == MATRIX_GT || st->relation == MATRIX_GE;
    MatrixNode *member[2] = {swapped ? st->right : st->left, swapped ? st->left : st->right};
    MatrixValue value[2] = {swapped ? right : left, swapped ? left : right};
    certificate_length = 0;
    certificate_broken = 0;

    /* L'enunciato e la sua verità; poi i testimoni, membro per membro
     * nell'ordine in cui sono scritti. Lo 0 che sta per la matrice nulla
     * non ha operandi, e non ne chiede. */
    cert_add("certificate matrices\nstatement (%s", words[st->relation]);
    for (int side = 0; side < 2; side++) {
        cert_add(" ");
        if (matrix_is_zero(member[side]) && value[side].is_matrix) cert_add("(zero %d %d)", value[side].matrix.rows, value[side].matrix.cols);
        else matrix_cert_node(member[side]);
    }
    cert_add(")\nclaim %s\n", truth ? "true" : "false");
    for (int side = 0; side < 2; side++) matrix_cert_witnesses(member[side]);
    cert_add("end\n");
}

/* 32g. CON UNA LETTERA: UN DETERMINANTE È UN POLINOMIO
 *
 * A che cosa serve. "Per quali k la matrice è singolare?", "quali sono gli
 * autovalori?": negli esercizi il determinante ha dentro una lettera, e la
 * domanda è un'equazione o una disequazione in quella lettera.
 *
 *     \{k \in \mathbb{R} \mid \det \begin{pmatrix} k & 1 \\ 1 & k \end{pmatrix} = 0\}
 *     A = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix} \implies \{s \in \mathbb{R} \mid \det(A - sI) = 0\}
 *     \forall k \in \mathbb{R}\ (\det \begin{pmatrix} k & 1 \\ 1 & k \end{pmatrix} = 0 \iff k = 1 \lor k = -1)
 *
 * È ciò che si fa a mano: si sviluppa il determinante, si ottiene un
 * polinomio, e l'esercizio diventa un esercizio di algebra, che il programma
 * sa già fare (la tabella dei segni, 18p; un parametro, 18t). Qui si fa solo
 * il primo passo: ogni determinante, e ogni traccia, viene sostituito nel
 * testo dal suo polinomio, e l'enunciato che ne risulta si rilegge da capo e
 * passa a prove_quantified(), come fa 18v-8 con le applicazioni. Il secondo
 * enunciato qui sopra diventa \{s \in \mathbb{R} \mid (s^{2} - 4 s + 3) = 0\}.
 *
 * Come si trova il polinomio. Non con un conto simbolico sulle matrici: con
 * il conto sui numeri di questo capitolo, fatto in tanti punti quanti
 * bastano. Se gli elementi sono polinomi nelle lettere, il determinante è un
 * polinomio nelle lettere, e di ogni lettera si sa limitare il grado: quello
 * di una somma è al più il più grande dei due, quello di un prodotto la
 * somma, quello del determinante di una matrice n x n al più n volte quello
 * degli elementi, perché il determinante è una somma di prodotti di n
 * elementi. E un polinomio di grado al più d in una lettera è determinato
 * dai suoi valori in d + 1 punti: due polinomi così che coincidono in d + 1
 * punti hanno per differenza un polinomio di grado al più d con d + 1
 * radici, cioè il polinomio nullo. Con più lettere lo stesso ragionamento,
 * una lettera alla volta, dice che bastano i valori sulla griglia dei punti
 * con la prima lettera in 0, ..., d_0, la seconda in 0, ..., d_1, e così via.
 *
 *   g1. le lettere dell'espressione, e per ognuna il limite del grado;
 *   g2. il valore dell'espressione in ogni punto della griglia: è il conto
 *       di 32d con i numeri al posto delle lettere, con l'eliminazione e i
 *       suoi testimoni;
 *   g3. dai valori ai coefficienti, una lettera alla volta;
 *   g4. il polinomio scritto, e il certificato dello sviluppo;
 *   g5. l'enunciato riscritto, e il verdetto.
 *
 * IL CONTROLLO INDIPENDENTE. Il polinomio trovato è un'interpolazione: con
 * un limite del grado sbagliato sarebbe un altro polinomio, senza che nulla
 * qui se ne accorga. Per questo ogni sviluppo ha il suo certificato, nella
 * notazione con le lettere del capitolo 17 di checker.c (17d), e senza che
 * il verificatore lo accetti non si sostituisce nulla. Là il determinante si
 * ricalcola per un'altra strada: con la sua definizione, la formula di
 * Leibniz, sui polinomi, senza punti e senza eliminazione. I due conti non
 * hanno in comune né il metodo né l'aritmetica. E il polinomio che il
 * certificato nomina non sono i coefficienti trovati: è il testo che entra
 * nell'enunciato, riletto. Così anche un errore nello scriverlo è un altro
 * polinomio, e viene respinto.
 *
 * CHE COSA È CERTIFICATO. Il verdetto poggia su due certificati: quello
 * dello sviluppo ("per ogni valore delle lettere il determinante vale questo
 * polinomio") e quello dell'enunciato che resta, quando il suo metodo lo
 * scrive. Che l'enunciato che resta sia quello di partenza con il polinomio
 * al posto del determinante è lettura, come in ogni altro certificato. Se
 * l'enunciato che resta non ha un certificato il verdetto lo dice, e dice
 * che lo sviluppo ce l'ha.
 *
 * CHE COSA RESTA FUORI, con il motivo nel verdetto: il rango e l'inversa
 * accanto a una lettera dentro un'espressione (dipendono dal valore della
 * lettera; un rango confrontato con un numero è invece un fatto che il
 * capitolo 33 discute per casi, 33h); un confronto tra matrici con una
 * lettera; elementi che non sono polinomi (una divisione per una lettera,
 * una radice, una funzione); più di MAX_LETTERS lettere. Un enunciato con
 * una lettera deve dire dove sta, con \mathbb: senza, è del resto del
 * capitolo, che le lettere le rifiuta.
 */

#define MAX_LETTER_DEGREE 24    /* limite del grado in una lettera */
#define MAX_LETTER_POINTS 4096  /* punti della griglia, e coefficienti del polinomio */

static const char *const LETTER_SHAPE =
    "accanto a una lettera gli elementi di una matrice sono polinomi nelle lettere minuscole: niente divisioni per una lettera, radici, funzioni o nomi di matrici";
const char *const LETTER_CASES =
    "con una lettera l'inversa cambia con il valore della lettera, e un rango si discute solo quando è confrontato con un numero, "
    "\\operatorname{rank} A = 2: qui la discussione per casi non è ancora trattata";
static const char *const LETTER_MATRIX =
    "in un enunciato con una lettera una matrice sta solo dentro un determinante o una traccia: i confronti tra matrici con una lettera non sono ancora trattati";

/* Il limite del grado di un'espressione in ognuna delle lettere di
 * letter_name[]: at[i] per la lettera i. */
typedef struct {
    long long at[MAX_LETTERS];
} LetterDegree;

/* Ritorna il limite del grado della somma (sum a 0: il più grande dei due,
 * lettera per lettera) o del prodotto (sum a 1: la somma) di due
 * espressioni con i limiti a e b. */
static LetterDegree degree_join(LetterDegree a, LetterDegree b, int sum) {
    for (int i = 0; i < MAX_LETTERS; i++) a.at[i] = sum ? a.at[i] + b.at[i] : a.at[i] > b.at[i] ? a.at[i] : b.at[i];
    return a;
}

/* Ritorna il limite del grado di un prodotto di times fattori con il limite
 * a. Oltre MAX_LETTER_DEGREE il numero non serve più, e si ferma lì vicino
 * per non uscire dagli interi. */
static LetterDegree degree_times(LetterDegree a, long long times) {
    for (int i = 0; i < MAX_LETTERS; i++) a.at[i] = a.at[i] && times > MAX_LETTER_DEGREE ? MAX_LETTER_DEGREE + 1 : a.at[i] * times;
    return a;
}

/* Ritorna 1 se un'espressione con il limite a non contiene lettere. */
static int degree_free(LetterDegree a) {
    for (int i = 0; i < MAX_LETTERS; i++)
        if (a.at[i]) return 0;
    return 1;
}

/* g1. Ritorna il limite del grado del numero scritto da node in ognuna delle
 * lettere, e aggiunge a letter_name[] quelle che incontra per la prima
 * volta, con il valore zero. Annota un errore se node non è un polinomio
 * nelle lettere: gli alberi accettati sono quelli di matrix_number(), con
 * le divisioni solo per un numero e le potenze negative solo di un numero. */
static LetterDegree letter_degree_number(const Node *node) {
    LetterDegree none = {{0}}, a;
    long long exponent;
    if (failure) return none;
    switch (node->kind) {
    case N_NUM:
        return none;
    case N_VAR: {
        /* Solo le minuscole. Una maiuscola è il nome di una matrice (capitolo
         * 31), e tra gli elementi il capitolo 9 la leggerebbe come una
         * lettera qualsiasi: una matrice a blocchi, \begin{pmatrix} A & 0 \\
         * 0 & k \end{pmatrix}, diventerebbe una 2 x 2 con un numero A. */
        int i = 0;
        if (node->name >= 128 || !islower(node->name)) break;
        while (i < letter_count && letter_name[i] != node->name) i++;
        if (i == MAX_LETTERS) { fail("troppe lettere diverse in un determinante"); return none; }
        if (i == letter_count) {
            letter_name[letter_count++] = node->name;
            letter_value[i] = frac_int(0);
        }
        none.at[i] = 1;
        return none;
    }
    case N_NEG:
        return letter_degree_number(node->a);
    case N_ADD: case N_SUB: case N_MUL:
        a = letter_degree_number(node->a);
        return degree_join(a, letter_degree_number(node->b), node->kind == N_MUL);
    case N_DIV:
        a = letter_degree_number(node->a);
        if (!degree_free(letter_degree_number(node->b))) break;
        return a;
    case N_POW:
        a = letter_degree_number(node->a);
        if (!matrix_exponent_value(node->b, &exponent) || (exponent < 0 && !degree_free(a))) break;
        return degree_times(a, exponent < 0 ? 0 : exponent);
    default:
        break;
    }
    fail(LETTER_SHAPE);
    return none;
}

/* g1. Ritorna il limite del grado dell'espressione node in ognuna delle
 * lettere (vedi la testa del paragrafo), e ne raccoglie le lettere in
 * letter_name[]. Annota un errore per ciò che con una lettera non si
 * tratta: il rango, l'inversa, un elemento che non è un polinomio. */
static LetterDegree letter_degree(MatrixNode *node) {
    LetterDegree none = {{0}}, a;
    if (failure) return none;
    switch (node->kind) {
    case M_SCALAR:
        return letter_degree_number(node->scalar);
    case M_TABLE:
        for (int i = 0; i < node->rows * node->cols; i++) none = degree_join(none, letter_degree_number(node->entry[i]), 0);
        return none;
    case M_IDENTITY:
        return none;
    case M_NEG: case M_TRANSPOSE: case M_TRACE:
        return letter_degree(node->a);
    case M_ADD: case M_SUB: case M_MUL:
        a = letter_degree(node->a);
        return degree_join(a, letter_degree(node->b), node->kind == M_MUL);
    case M_POWER:
        /* Un esponente negativo: l'inverso di un numero senza lettere, mai
         * un'inversa. */
        a = letter_degree(node->a);
        if (node->power < 0 && (matrix_shape(node->a) != SHAPE_NUMBER || !degree_free(a))) {
            fail(matrix_shape(node->a) == SHAPE_NUMBER ? LETTER_SHAPE : LETTER_CASES);
            return none;
        }
        return degree_times(a, node->power < 0 ? 0 : node->power);
    case M_DET: {
        /* n volte il grado degli elementi: n sono le righe dell'argomento,
         * e le dice il suo valore con le lettere a zero. */
        a = letter_degree(node->a);
        MatrixValue value = matrix_eval(node->a, 0);
        return failure ? none : degree_times(a, value.is_matrix ? value.matrix.rows : 1);
    }
    default:
        fail(LETTER_CASES);
        return none;
    }
}

/* I coefficienti del polinomio di g3, e prima i valori di g2 sulla griglia.
 * Il posto e_0 + (d_0 + 1) e_1 + (d_0 + 1)(d_1 + 1) e_2 + ... è quello del
 * punto in cui la lettera i vale e_i, e poi del coefficiente del monomio in
 * cui la lettera i ha l'esponente e_i; d_i è il limite del grado. */
static _Thread_local Frac letter_grid[MAX_LETTER_POINTS];

/* g2, g3. Calcola il polinomio che l'espressione node, che vale un numero,
 * è nelle lettere di letter_name[], con i limiti dei gradi degree: mette i
 * coefficienti in letter_grid[] e ne ritorna il numero, 0 dopo un errore. */
static int letter_polynomial(MatrixNode *node, LetterDegree degree) {
    int size = 1;
    for (int i = 0; i < letter_count; i++) {
        if (degree.at[i] > MAX_LETTER_DEGREE || size * (degree.at[i] + 1) > MAX_LETTER_POINTS) {
            fail("il determinante ha un grado troppo alto nelle sue lettere");
            return 0;
        }
        size *= (int)degree.at[i] + 1;
    }

    /* g2. I valori: nel punto numero p la lettera i vale la cifra i di p,
     * scritto con le basi d_0 + 1, d_1 + 1, ... La memoria di ogni conto si
     * restituisce: resta solo il numero. */
    for (int p = 0; p < size && !failure; p++) {
        size_t mark = arena_used;
        for (int i = 0, rest = p; i < letter_count; rest /= (int)degree.at[i] + 1, i++) letter_value[i] = frac_int(rest % ((int)degree.at[i] + 1));
        MatrixValue value = matrix_eval(node, 0);
        if (!failure && value.is_matrix) fail(LETTER_MATRIX);
        letter_grid[p] = value.number;
        arena_used = mark;
    }

    /* g3. Dai valori ai coefficienti, una lettera alla volta: lungo la
     * lettera i la griglia è fatta di file di d + 1 posti, distanti stride,
     * e ogni fila è un polinomio di grado al più d in quella lettera, dato
     * dai valori nei punti 0, 1, ..., d.
     *
     * Le differenze divise di Newton lo scrivono come
     *
     *     c_0 + c_1 x + c_2 x (x - 1) + ... + c_d x (x - 1) ... (x - d + 1):
     *
     * c_j è la differenza divisa dei primi j + 1 punti, e ogni differenza
     * divisa è (quella dei punti dopo il primo - quella dei punti prima
     * dell'ultimo) / (ultimo punto - primo punto), che qui è il numero k
     * dei passi. Il giro su j all'indietro le calcola sul posto.
     *
     * Poi lo schema di Horner svolge i prodotti, da c_d in giù: a ogni
     * passo il polinomio P già svolto diventa P (x - j) + c_j. I suoi
     * coefficienti stanno nei posti da j + 1 a d, e quelli nuovi vanno nei
     * posti da j a d: nel posto t entra il coefficiente che stava lì (il
     * prodotto per x lo sposta di un grado; nel posto j c'è c_j) meno j
     * volte quello del posto dopo. */
    for (int i = 0, stride = 1; i < letter_count && !failure; stride *= (int)degree.at[i] + 1, i++) {
        int d = (int)degree.at[i];
        for (int first = 0; first < size; first++) {
            Frac *row = &letter_grid[first];
            if (first / stride % (d + 1)) continue;
            for (int k = 1; k <= d; k++)
                for (int j = d; j >= k; j--) row[j * stride] = frac_div(frac_add(row[j * stride], frac_neg(row[(j - 1) * stride])), frac_int(k));
            for (int j = d - 1; j >= 0; j--)
                for (int t = j; t < d; t++) row[t * stride] = frac_add(row[t * stride], frac_neg(frac_mul(frac_int(j), row[(t + 1) * stride])));
        }
    }
    return failure ? 0 : size;
}

/* Mette in exponent[] gli esponenti delle lettere nel monomio che ha il
 * posto place in letter_grid[], con i limiti dei gradi degree. */
static void letter_exponents(int place, LetterDegree degree, int *exponent) {
    for (int i = 0; i < letter_count; place /= (int)degree.at[i] + 1, i++) exponent[i] = place % ((int)degree.at[i] + 1);
}

/* g4. Aggiunge a text, di size byte, il polinomio di letter_grid[], che ha
 * count coefficienti: in LaTeX, dai gradi più alti, scritto in modo che il
 * capitolo 9 lo rilegga uguale. */
static void letter_latex(int count, LetterDegree degree, char *text, size_t size) {
    size_t start = strlen(text);
    for (int place = count - 1; place >= 0 && !failure; place--) {
        char body[32 * MAX_LETTERS] = "";
        int exponent[MAX_LETTERS];
        letter_exponents(place, degree, exponent);
        for (int i = 0; i < letter_count; i++) {
            if (exponent[i] == 0) continue;
            text_add(body, sizeof body, "%s%c", body[0] ? " " : "", letter_name[i]);
            if (exponent[i] > 1) text_add(body, sizeof body, "^{%d}", exponent[i]);
        }
        term_latex(letter_grid[place], body, text + start, size - start);
    }
    if (!text[start]) text_add(text, size, "0");
}

/* g4. Scrive in certificate_text il certificato dello sviluppo: per ogni
 * valore delle lettere, l'espressione node vale il polinomio written (17d
 * di checker.c). Va chiamata con almeno una lettera in letter_name[]. */
static void letter_certificate(MatrixNode *node, const Node *written) {
    certificate_length = 0;
    certificate_broken = 0;
    cert_add("certificate matrices\nletters");
    for (int i = 0; i < letter_count; i++) cert_add(" %c", letter_name[i]);
    cert_add("\nstatement (= ");
    matrix_cert_node(node);
    cert_add(" ");
    matrix_cert_number(written);
    cert_add(")\nclaim true\nend\n");
}

/* g1-g4. Sviluppa l'espressione node, che è scritta nel testo da from a to:
 * ne trova il polinomio, lo fa certificare, e aggiunge il polinomio tra
 * parentesi a text (di size byte), il suo certificato a certificates (di
 * bytes byte) e la riga "espressione = polinomio" alla dimostrazione in
 * corso. Ritorna NULL se riesce; altrimenti il motivo, e allora *rejected
 * dice se è il verificatore ad aver respinto lo sviluppo.
 *
 * Il certificato non parla dei coefficienti trovati: parla del polinomio
 * così com'è scritto nel testo, riletto dal lettore delle espressioni. È
 * quel testo che entra nell'enunciato, ed è quel lettore che poi lo legge:
 * un errore nello scriverlo darebbe un altro polinomio, che il verificatore
 * respinge. */
static const char *letter_expand(MatrixNode *node, const char *from, const char *to, char *text, size_t size,
                                 char *certificates, size_t bytes, int *rejected) {
    static _Thread_local char problem[512];
    const char *why = "il certificato dello sviluppo non si può scrivere", *certificate = certificate_text;
    size_t start = strlen(text);
    *rejected = 0;

    /* g1-g3. Le lettere, i gradi, il polinomio. */
    letter_count = 0;
    LetterDegree degree = letter_degree(node);
    int count = letter_polynomial(node, degree);
    if (failure) return failure;

    /* g4. Il polinomio tra parentesi, e la riga della dimostrazione. */
    text_add(text, size, "(");
    letter_latex(count, degree, text, size);
    text_add(text, size, ")");
    proof_add("$%.*s = %s$. ", (int)(to - from), from, text + start);
    if (failure || proof_broken) return failure ? failure : "dimostrazione troppo lunga da scrivere";

    /* g4. Il polinomio riletto. Il lettore è a metà dell'enunciato: lo si
     * lascia dov'era. */
    ParserState here = parser_save();
    const char *here_consumed = consumed;
    syntax_error = NULL;
    cursor = text + start;
    next_token();
    Node *written = parse_expr();
    int reread = !syntax_error && token.kind == T_END;
    parser_restore(here);
    consumed = here_consumed;
    if (!reread) return "il polinomio di uno sviluppo, scritto, non si rilegge";

    /* g4. Il certificato: con le lettere quello di 17d; senza, l'enunciato
     * "espressione = numero" con i testimoni di 32f. */
    if (letter_count) {
        letter_certificate(node, written);
    } else {
        MatrixNode *number = matrix_node(M_SCALAR, NULL, NULL);
        number->scalar = written;
        const MatrixStatement stated = {node, number, MATRIX_EQ, 0, {NULL}};
        const MatrixValue value = {0, letter_grid[0], {0, 0, NULL}};
        matrix_certificate(&stated, value, value, 1);
    }
    CkAnswer checked = certificate_broken ? CK_UNSUPPORTED : ck_check(&certificate, &why, checker_steps());
    if (checked != CK_ACCEPTED) {
        *rejected = checked == CK_REJECTED;
        snprintf(problem, sizeof problem, checked == CK_REJECTED ? "il verificatore indipendente ha respinto lo sviluppo di un determinante: %s"
                                                                 : "il verificatore non sa controllare lo sviluppo di un determinante: %s", why);
        return problem;
    }
    text_add(certificates, bytes, "%s%s", certificates[0] ? "\n" : "", certificate_text);
    return failure;
}

/* g5. Decide l'enunciato formula, che ha una matrice scritta per esteso e
 * dice dove stanno le sue lettere (vedi la testa del paragrafo): sviluppa
 * ogni determinante e ogni traccia, e fa decidere a prove_quantified()
 * l'enunciato che resta. Svuota l'arena: i risultati di chiamate precedenti
 * non sono più validi. */
static Verdict prove_matrix_letters(const char *formula) {
    static _Thread_local char rewritten[2 * MAX_FORMULA], expansions[4 * MAX_FORMULA], certificates[CERTIFICATE_BYTES], method[256], reason[768];
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, MATRIX_METHOD, NULL, NULL};
    MatrixStatement names;

    /* Ripartenza da zero, e le definizioni, se l'enunciato comincia con il
     * nome di una matrice: danno un nome a degli alberi, e una che
     * l'enunciato non usa non viene guardata. */
    proof_reset();
    arena_used = arena_keep;
    failure = NULL;
    matrix_work = 0;
    rewritten[0] = certificates[0] = 0;
    memset(&names, 0, sizeof names);
    matrix_start(formula);
    if (token.kind == T_LETTER && isupper(token.ch)) matrix_definitions(&names);

    /* I fattori da sviluppare, uno dopo l'altro: ciò che sta tra l'uno e
     * l'altro si copia com'è. `copied` è dove la copia è arrivata. */
    const char *copied = token.start;
    while (token.kind != T_END && !syntax_error && !failure) {
        if (!matrix_starts_here()) { next_token(); continue; }
        const char *from = token.start;
        MatrixNode *node = matrix_factor();
        if (syntax_error) break;
        int rejected;
        text_add(rewritten, sizeof rewritten, "%.*s", (int)(from - copied), copied);
        const char *problem = letter_expand(node, from, consumed, rewritten, sizeof rewritten, certificates, sizeof certificates, &rejected);
        if (problem && !failure) {
            /* Lo sviluppo c'è, ma il verificatore non lo ha accettato. */
            if (rejected) unjustified_steps++;
            return (Verdict){NOT_PROVED, 0, 0, 0, problem, NULL, NULL, NULL, NULL, NULL};
        }
        copied = consumed;
    }
    if (!syntax_error && !failure) text_add(rewritten, sizeof rewritten, "%s", copied);
    if (syntax_error || failure) { verdict.reason = syntax_error ? syntax_error : failure; return verdict; }
    if (strlen(rewritten) >= MAX_FORMULA || proof_length >= sizeof expansions) {
        verdict.reason = "enunciato troppo lungo, una volta sviluppati i determinanti";
        return verdict;
    }
    memcpy(expansions, proof_text, proof_length + 1);

    /* L'enunciato che resta, da capo. Se è deciso, il metodo dice anche
     * dello sviluppo, e la dimostrazione lo riporta in fondo. Senza nessuno
     * sviluppo (le matrici stavano solo in definizioni non usate) è un
     * enunciato come gli altri. */
    verdict = prove_quantified(rewritten);
    if (!certificates[0]) return verdict;
    if (verdict.outcome != PROVED && verdict.outcome != REFUTED && verdict.outcome != SOLVED) return verdict;
    snprintf(method, sizeof method, "%s, dopo aver sviluppato determinanti e tracce in polinomi", verdict.method ? verdict.method : MATRIX_METHOD);
    verdict.method = method;
    proof_add(" The statement decided here is the given one with each determinant or trace replaced by its expansion, "
              "a polynomial found from exact values at enough points and confirmed by the independent checker: %s"
              "The statement becomes $%s$.", expansions, rewritten);
    if (proof_broken) return (Verdict){UNSUPPORTED, 0, 0, 0, "dimostrazione troppo lunga da scrivere", NULL, NULL, NULL, NULL, NULL};
    verdict.proof = proof_text;

    /* I certificati: quello dell'enunciato che resta, se c'è, e dopo di lui
     * quelli degli sviluppi. Se manca, il motivo dice che cosa è certificato
     * lo stesso. */
    if (verdict.certificate) {
        cert_add("\n%s", certificates);
        verdict.certificate = certificate_text;
        if (!certificate_broken) return verdict;
        verdict.reason = "i certificati sono troppo lunghi da scrivere insieme";
    }
    snprintf(reason, sizeof reason, "lo sviluppo di determinanti e tracce ha il suo certificato, verificato; l'enunciato che ne risulta no%s%s",
             verdict.reason ? ", " : "", verdict.reason ? verdict.reason : "");
    verdict.reason = reason;
    verdict.certificate = NULL;
    return verdict;
}

/* 32h. IL VERDETTO */

/* Prova a dimostrare, smentire o risolvere l'enunciato sulle matrici scritto
 * in formula (vedi la testa del capitolo). Svuota l'arena: i risultati di
 * chiamate precedenti non sono più validi.
 *
 * Una richiesta si risolve in due tempi: si calcola il valore, lo si scrive,
 * e l'enunciato "espressione = valore scritto" passa da capo per questa
 * stessa funzione, che lo rilegge e lo fa certificare. Così ciò che si
 * consegna è ciò che è stato controllato: un errore nello scrivere il
 * valore cambia ciò che si rilegge, e il verificatore lo respinge.
 *
 * Un enunciato che dice dove stanno le sue lettere, con \mathbb, è di 32g. */
Verdict prove_matrix(const char *formula) {
    static _Thread_local char answer[3 * MAX_FORMULA], reread[4 * MAX_FORMULA], note[256], problem[512];
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, MATRIX_METHOD, NULL, NULL};
    MatrixStatement st;

    /* Nessuna lettera ha un valore, se non dentro 32g: anche dopo un suo
     * conto interrotto a metà. */
    letter_count = 0;
    if (strstr(formula, "\\mathbb")) return prove_matrix_letters(formula);

    /* Ripartenza da zero per il nuovo enunciato, e lettura. */
    proof_reset();
    arena_used = arena_keep;
    failure = NULL;
    matrix_work = 0;
    if (!parse_matrix_statement(formula, &st)) { verdict.reason = syntax_error; return verdict; }

    /* Le definizioni, nell'ordine in cui sono scritte: ognuna deve avere un
     * valore da sola, senza che un contesto le presti una dimensione. */
    for (int i = 0; i < st.definitions && !failure; i++) matrix_eval(st.definition[i], 0);

    /* Una richiesta: il valore, scritto, e l'enunciato che lo afferma. */
    if (st.relation == MATRIX_ASKED) {
        MatrixValue value = matrix_eval(st.left, 0);
        if (!failure) matrix_put(value);
        if (failure || proof_broken || proof_length >= sizeof answer || strlen(formula) + proof_length + 4 >= sizeof reread) {
            verdict.reason = failure ? failure : "risultato troppo lungo da scrivere";
            return verdict;
        }
        memcpy(answer, proof_text, proof_length + 1);
        snprintf(reread, sizeof reread, "%s = %s", formula, answer);
        Verdict stated = prove_matrix(reread);
        if (stated.outcome != PROVED) {
            /* Riletta e falsa: il valore scritto non è quello calcolato. Il
             * motivo della chiamata interna può stare in `problem`, dove va
             * scritto quello nuovo: prima lo si copia, accorciato quanto
             * basta perché ci stia con ciò che lo precede. */
            char inner[256];
            if (stated.outcome == REFUTED) unjustified_steps++;
            snprintf(inner, sizeof inner, "%s", stated.reason ? stated.reason : "risulta falsa");
            snprintf(problem, sizeof problem, "la risposta calcolata, riletta come enunciato, non è stata dimostrata: %s", inner);
            return (Verdict){NOT_PROVED, 0, 0, 0, problem, NULL, NULL, NULL, NULL, NULL};
        }
        stated.outcome = SOLVED;
        stated.detail = answer;
        return stated;
    }

    /* I due membri: prima quello che sa la propria dimensione (32d). Lo 0
     * da solo accanto a una matrice è la matrice nulla. */
    MatrixValue left, right;
    if (matrix_shape(st.right) > matrix_shape(st.left)) {
        right = matrix_eval(st.right, 0);
        left = matrix_eval(st.left, matrix_want(M_ADD, right, 0, 0));
    } else {
        left = matrix_eval(st.left, 0);
        right = matrix_eval(st.right, matrix_want(M_ADD, left, 1, 0));
    }
    if (!failure && (st.relation == MATRIX_EQ || st.relation == MATRIX_NEQ)) {
        if (matrix_is_zero(st.right) && left.is_matrix) right = (MatrixValue){1, {0, 1}, matrix_zero(left.matrix.rows, left.matrix.cols)};
        if (matrix_is_zero(st.left) && right.is_matrix) left = (MatrixValue){1, {0, 1}, matrix_zero(right.matrix.rows, right.matrix.cols)};
    }
    int truth = matrix_holds(left, right, st.relation, note, sizeof note);
    if (failure) { verdict.reason = failure; return verdict; }

    /* La dimostrazione scritta: i due valori, e che cosa ne segue. */
    proof_add("Exact computation with rational numbers. The left-hand side is $");
    matrix_put(left);
    proof_add("$. The right-hand side is $");
    matrix_put(right);
    proof_add(truth ? "$. Hence the stated relation holds." : "$. Hence the stated relation does not hold.");
    if (proof_broken) { verdict.reason = "dimostrazione troppo lunga da scrivere"; return verdict; }

    /* Il certificato, e la risposta del verificatore (vedi "Il controllo
     * indipendente" in testa al capitolo). */
    const char *why = "il certificato non si può scrivere", *text = certificate_text;
    matrix_certificate(&st, left, right, truth);
    CkAnswer checked = certificate_broken ? CK_UNSUPPORTED : ck_check(&text, &why, checker_steps());
    if (checked != CK_ACCEPTED) {
        if (checked == CK_REJECTED) unjustified_steps++;
        snprintf(problem, sizeof problem, checked == CK_REJECTED ? "il verificatore indipendente ha respinto il certificato: %s"
                                                                 : "il verificatore non sa controllare il certificato: %s", why);
        return (Verdict){NOT_PROVED, 0, 0, 0, problem, NULL, NULL, NULL, NULL, NULL};
    }
    verdict.outcome = truth ? PROVED : REFUTED;
    verdict.note = truth ? NULL : note;
    verdict.proof = proof_text;
    verdict.certificate = certificate_text;
    return verdict;
}

/* Ritorna 1 se formula scrive una matrice per esteso, con uno degli
 * ambienti di matrix_environments[] (capitolo 31): è un enunciato di questo
 * capitolo, e prove_core() lo manda qui. Un altro ambiente, come cases, non
 * conta. */
int uses_matrices(const char *formula) {
    for (const char *p = strstr(formula, "\\begin"); p; p = strstr(p + 1, "\\begin")) {
        const char *name = p + 6;
        while (isspace((unsigned char)*name)) name++;
        if (*name != '{') continue;
        for (size_t i = 0; i < sizeof matrix_environments / sizeof *matrix_environments; i++) {
            size_t length = strlen(matrix_environments[i].name);
            if (strncmp(name + 1, matrix_environments[i].name, length) == 0 && name[1 + length] == '}') return 1;
        }
    }
    return 0;
}

/* =============================================================================
 * 33. SISTEMI LINEARI: L'INSIEME DELLE SOLUZIONI
 * ============================================================================
 *
 * Decide gli enunciati del paragrafo 31s (parser.c): l'insieme delle
 * soluzioni di un sistema di equazioni lineari, e che cosa se ne dice. "Le
 * soluzioni sono queste", "il sistema è impossibile", "questa terna è una
 * soluzione". Senza relazione l'enunciato è una richiesta, e la risposta è
 * l'insieme scritto come nei libri: una soluzione particolare più i
 * parametri liberi,
 *
 *     \{(0, \frac{4}{5}, \frac{1}{5}) + t (1, -1, 0) \mid t \in \mathbb{R}\}.
 *
 * COME
 *
 * Il metodo è uno solo, l'eliminazione di Gauss del capitolo 32, e non
 * guarda quante sono le equazioni o le incognite:
 *
 *   33a. dal testo alle matrici: i coefficienti delle incognite e i termini
 *        noti, cioè il sistema scritto come A x = b;
 *   33b. l'eliminazione, e i testimoni che lascia;
 *   33c. che cosa dice l'enunciato, e che cosa lo mostra;
 *   33d. la dimostrazione scritta e il certificato;
 *   33e. le soluzioni scritte, e il sì del verificatore;
 *   33f. i polinomi in una lettera e le matrici di polinomi, che servono con
 *        un parametro;
 *   33g. con un parametro, il caso generico: il rango e le soluzioni per
 *        tutti i valori che non annullano un polinomio;
 *   33h. la discussione: i valori speciali, e ogni fatto che diventa una
 *        condizione sul parametro;
 *   33i. il verdetto, e la risposta di una richiesta, riletta.
 *
 * CHE COSA VUOL DIRE UN ENUNCIATO
 *
 *   - Una soluzione è un vettore di numeri reali che soddisfa tutte le
 *     equazioni. I coefficienti sono razionali, e allora le soluzioni reali
 *     sono descritte dagli stessi vettori razionali: l'eliminazione usa solo
 *     le quattro operazioni.
 *   - Due insiemi sono uguali se hanno gli stessi elementi. L'insieme
 *     scritto \{p + t v + s w \mid t, s \in \mathbb{R}\} può avere più
 *     parametri del necessario, o vettori dipendenti: è lo stesso insieme.
 *   - Un insieme scritto con vettori di un'altra lunghezza non è confrontato:
 *     l'enunciato non ha senso, NON SUPPORTATO.
 *
 * IL CONTROLLO INDIPENDENTE
 *
 * Ha tre livelli. La lettura: i coefficienti si ricavano trattando ogni
 * equazione come una forma di primo grado nelle incognite, e si
 * ricontrollano calcolando l'equazione com'è scritta in abbastanza punti
 * (33a). L'eliminazione: ogni cosa che trova esce con un testimone, che si
 * ricontrolla con dei prodotti prima di usarla (33b), come nel capitolo 32.
 * Il verificatore: ogni verdetto vuole che checker.c abbia accettato il
 * certificato (33d), che porta il sistema, l'insieme scritto e gli stessi
 * testimoni; lì non c'è eliminazione, solo somme, prodotti e confronti.
 *
 * PERCHÉ COSÌ
 *
 * I testimoni sono scelti perché il controllo sia il più corto da credere, e
 * non chieda teoremi sul rango (33b): che un vettore sia una soluzione è un
 * prodotto; che non ce ne siano è una combinazione delle equazioni che dà
 * 0 = c con c diverso da zero; che siano tutte quelle scritte è un'identità
 * tra matrici, G A + V T = I, da cui ogni soluzione si ricostruisce. Il
 * teorema di Rouché-Capelli, con i due ranghi, direbbe le stesse cose, ma
 * chiederebbe al verificatore due testimoni del rango e il teorema della
 * dimensione: qui basta moltiplicare.
 *
 * Con un parametro il metodo resta quello: non c'è una formula per "il
 * sistema 3 x 3 con il parametro sulla diagonale". Si sceglie un minore
 * guardando i numeri in un valore qualsiasi, lo si usa per tutti i valori
 * che non ne annullano il determinante (le formule di Cramer, controllate
 * moltiplicando), e negli altri si rifà il conto sui numeri. Le celle di 18t
 * qui si riducono ai valori speciali e al loro complemento: un rango cambia
 * solo dove un polinomio si annulla, non attraversando un intervallo.
 */

static const char *const LINEAR_METHOD = "con l'eliminazione di Gauss";
static const char *const LINEAR_SHAPE =
    "le equazioni di un sistema lineare sono di primo grado nelle incognite, e un insieme scritto lo è nei suoi parametri: "
    "niente prodotti o potenze di due di loro, né una di loro a denominatore o dentro una funzione";

/* 33a. DAL TESTO ALLE MATRICI
 *
 * Un'equazione di primo grado nelle incognite x_1, ..., x_n si scrive in un
 * modo solo come a_1 x_1 + ... + a_n x_n = b: i numeri a_j sono una riga
 * della matrice A dei coefficienti, b un elemento della colonna dei termini
 * noti. Per trovarli ogni membro si calcola come una forma di primo grado,
 * cioè con i suoi n coefficienti e il suo termine noto: la somma e il
 * multiplo di due forme sono forme, il prodotto di due forme lo è solo se
 * una delle due è un numero, e ogni altra operazione (una potenza, una
 * funzione, un'incognita a denominatore) ferma il conto: l'equazione non è
 * lineare. L'equazione è allora (primo membro) - (secondo membro) = 0.
 *
 * LA LETTURA RICONTROLLATA. Una forma di primo grado è determinata dai suoi
 * valori nell'origine e negli n punti che hanno una sola coordinata uguale a
 * 1: lì vale il termine noto, e il termine noto più un coefficiente. Per
 * questo i coefficienti trovati si ricontrollano calcolando l'equazione
 * com'è scritta, con i numeri al posto delle incognite (matrix_number()), in
 * quegli n + 1 punti e in uno in più, che ha per coordinate i primi numeri
 * primi: un prodotto di due incognite preso per sbaglio come lineare si
 * annulla nei primi n + 1 e non nell'ultimo. I due conti leggono lo stesso
 * albero per due strade diverse.
 *
 * Lo stesso vale per un insieme scritto, con i parametri al posto delle
 * incognite: ogni componente del suo elemento generico è una forma di primo
 * grado nei parametri, p + t v + s w. */

/* Una forma di primo grado in un elenco di count lettere: at[i] è il
 * coefficiente della lettera i, at[count] il termine noto. */
typedef struct {
    Frac at[MAX_UNKNOWNS + 1];
} LinearForm;

/* Ritorna il posto in letter[], lungo count, della lettera scritta dal nodo
 * node (una variabile, o una lettera con il pedice numerico), oppure -1 se
 * node non è una di quelle. */
static int linear_place(const Node *node, const LinearLetter *letter, int count) {
    if (node->kind != N_VAR && (node->kind != N_SEQ || node->a->kind != N_NUM)) return -1;
    long long index = node->kind == N_SEQ ? node->a->value : -1;
    for (int i = 0; i < count; i++)
        if (letter[i].name == node->name && letter[i].index == index) return i;
    return -1;
}

/* Ritorna 1 se nel sotto-albero node compare una delle count lettere di
 * letter[]. */
static int linear_mentions(const Node *node, const LinearLetter *letter, int count) {
    if (!node) return 0;
    return linear_place(node, letter, count) >= 0 || linear_mentions(node->a, letter, count) || linear_mentions(node->b, letter, count) ||
           linear_mentions(node->c, letter, count);
}

/* Ritorna 1 se la forma f, in count lettere, è un numero: tutti i
 * coefficienti delle lettere sono zero. */
static int linear_is_number(const LinearForm *f, int count) {
    for (int i = 0; i < count; i++)
        if (f->at[i].num != 0) return 0;
    return 1;
}

/* Ritorna la somma delle forme a e b, in count lettere, con b moltiplicata
 * per il numero scale. */
static LinearForm linear_plus(LinearForm a, LinearForm b, Frac scale, int count) {
    for (int i = 0; i <= count; i++) a.at[i] = frac_add(a.at[i], frac_mul(scale, b.at[i]));
    return a;
}

/* Ritorna il prodotto delle forme a e b, in count lettere: una delle due
 * deve essere un numero, altrimenti annota che l'espressione non è di primo
 * grado. */
static LinearForm linear_times(LinearForm a, LinearForm b, int count) {
    LinearForm zero;
    for (int i = 0; i <= count; i++) zero.at[i] = frac_int(0);
    if (failure) return zero;
    if (linear_is_number(&a, count)) return linear_plus(zero, b, a.at[count], count);
    if (linear_is_number(&b, count)) return linear_plus(zero, a, b.at[count], count);
    fail(LINEAR_SHAPE);
    return zero;
}

/* Ritorna la forma di primo grado, nelle count lettere di letter[], che
 * l'albero node scrive (vedi la testa del paragrafo). Ciò che non contiene
 * quelle lettere è un numero di matrix_number(), con le sue regole. */
static LinearForm linear_form(const Node *node, const LinearLetter *letter, int count) {
    LinearForm form, a, b;
    for (int i = 0; i <= count; i++) form.at[i] = frac_int(0);
    if (failure) return form;
    if (!linear_mentions(node, letter, count)) {
        form.at[count] = matrix_number(node);
        return form;
    }
    int place = linear_place(node, letter, count);
    switch (node->kind) {
    case N_VAR: case N_SEQ:
        if (place < 0) break;
        form.at[place] = frac_int(1);
        return form;
    case N_NEG:
        return linear_plus(form, linear_form(node->a, letter, count), frac_int(-1), count);
    case N_ADD: case N_SUB:
        a = linear_form(node->a, letter, count);
        return linear_plus(a, linear_form(node->b, letter, count), frac_int(node->kind == N_ADD ? 1 : -1), count);
    case N_MUL:
        a = linear_form(node->a, letter, count);
        return linear_times(a, linear_form(node->b, letter, count), count);
    case N_DIV:
        /* Solo per un numero: a / b è a per 1 / b. */
        a = linear_form(node->a, letter, count);
        b = linear_form(node->b, letter, count);
        if (failure || !linear_is_number(&b, count)) break;
        return linear_plus(form, a, frac_div(frac_int(1), b.at[count]), count);
    default:
        break;
    }
    fail(LINEAR_SHAPE);
    return form;
}

/* Mette in point[], lungo count, il punto numero which tra quelli in cui si
 * ricontrolla una lettura: 0 è l'origine, da 1 a count il punto con la sola
 * coordinata which - 1 uguale a 1, count + 1 quello dei primi numeri primi
 * (vedi la testa del paragrafo). */
static void linear_sample(int which, int count, Frac *point) {
    static const int primes[MAX_UNKNOWNS] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (int i = 0; i < count; i++) point[i] = frac_int(which > count ? primes[i] : i == which - 1);
}

/* Ritorna il valore della forma f, in count lettere, nel punto point[]. */
static Frac linear_at(const LinearForm *f, const Frac *point, int count) {
    Frac value = f->at[count];
    for (int i = 0; i < count; i++) value = frac_add(value, frac_mul(f->at[i], point[i]));
    return value;
}

/* Annota che una lettura non ha superato il suo ricontrollo: un errore del
 * motore, che ferma il conto. */
static void linear_reading_failed(void) {
    if (failure) return;
    unjustified_steps++;
    fail("i coefficienti letti da un sistema non superano il ricontrollo fatto calcolando le equazioni in alcuni punti");
}

/* Mette in *a e *b la matrice dei coefficienti e la colonna dei termini noti
 * del sistema di st scritto con le incognite: una riga per equazione.
 * Ricontrolla la lettura (vedi la testa del paragrafo). */
static void linear_equations(const LinearStatement *st, Matrix *a, Matrix *b) {
    Frac point[MAX_UNKNOWNS];
    int n = st->dimension;
    *a = matrix_new(st->equations, n);
    *b = matrix_new(st->equations, 1);
    for (int i = 0; i < a->rows && !failure; i++) {
        LinearForm left = linear_form(st->left[i], st->unknown, n);
        LinearForm form = linear_plus(left, linear_form(st->right[i], st->unknown, n), frac_int(-1), n);
        for (int j = 0; j < n; j++) *matrix_at(*a, i, j) = form.at[j];
        *matrix_at(*b, i, 0) = frac_neg(form.at[n]);

        /* Il ricontrollo: l'equazione com'è scritta, nei punti. */
        for (int which = 0; which <= n + 1 && !failure; which++) {
            linear_sample(which, n, point);
            placed_letter = st->unknown;
            placed_value = point;
            placed_count = n;
            Frac direct = frac_add(matrix_number(st->left[i]), frac_neg(matrix_number(st->right[i])));
            placed_count = 0;
            if (!failure && frac_cmp(direct, linear_at(&form, point, n)) != 0) linear_reading_failed();
        }
    }
}

/* Ritorna 0, 1 oppure 2 secondo che l'espressione node non contenga il
 * vettore incognito, sia di primo grado in lui, o non lo sia: un prodotto di
 * due fattori che lo contengono, una sua potenza, un suo determinante. La
 * trasposta e la traccia sono di primo grado. */
static int linear_vector_degree(const MatrixNode *node) {
    int a = node->a ? linear_vector_degree(node->a) : 0, b = node->b ? linear_vector_degree(node->b) : 0;
    switch (node->kind) {
    case M_SCALAR:
        return node_has_variable(node->scalar, vector_name) ? 1 : 0;
    case M_TABLE:
        for (int i = 0; i < node->rows * node->cols; i++)
            if (node_has_variable(node->entry[i], vector_name)) return 2;
        return 0;
    case M_IDENTITY:
        return 0;
    case M_NEG: case M_TRANSPOSE: case M_TRACE:
        return a;
    case M_ADD: case M_SUB:
        return a > b ? a : b;
    case M_MUL:
        return a + b > 2 ? 2 : a + b;
    default:
        return a ? 2 : 0;
    }
}

/* Ritorna il valore di (primo membro) - (secondo membro) dell'equazione tra
 * matrici di st, con il vettore incognito uguale alla colonna x. Lo 0
 * scritto da solo come membro è la matrice nulla, e un'identità senza pedice
 * prende la dimensione dall'altro membro, come nel capitolo 32. */
static Matrix linear_residual(const LinearStatement *st, Matrix x) {
    MatrixValue left, right;
    vector_value = x;
    if (matrix_shape(st->matrix_right) > matrix_shape(st->matrix_left)) {
        right = matrix_eval(st->matrix_right, 0);
        left = matrix_eval(st->matrix_left, matrix_want(M_ADD, right, 0, 0));
    } else {
        left = matrix_eval(st->matrix_left, 0);
        right = matrix_eval(st->matrix_right, matrix_want(M_ADD, left, 1, 0));
    }
    if (failure) return (Matrix){0, 0, NULL};
    if (matrix_is_zero(st->matrix_right) && left.is_matrix) return left.matrix;
    if (matrix_is_zero(st->matrix_left) && right.is_matrix) return matrix_scale(right.matrix, frac_int(-1));
    if (!left.is_matrix || !right.is_matrix) { fail("con un vettore per incognita i due membri del sistema sono matrici: A x = B"); return (Matrix){0, 0, NULL}; }
    if (left.matrix.rows != right.matrix.rows || left.matrix.cols != right.matrix.cols) {
        fail("i due membri del sistema non hanno le stesse dimensioni");
        return (Matrix){0, 0, NULL};
    }
    return matrix_add(left.matrix, right.matrix, 1);
}

/* Mette in *a e *b la matrice dei coefficienti e la colonna dei termini noti
 * del sistema di st scritto con un vettore per incognita, A x = B: ogni
 * elemento dell'uguaglianza tra matrici è un'equazione.
 *
 * (primo membro) - (secondo membro) è una funzione di primo grado del
 * vettore x, perché x vi compare al più una volta in ogni prodotto
 * (linear_vector_degree()). Una funzione così è il suo valore nell'origine
 * più una parte lineare: il valore nell'origine è l'opposto dei termini
 * noti, e la colonna j dei coefficienti è il valore nel vettore che ha la
 * sola coordinata j uguale a 1, meno quello nell'origine. */
static void linear_vector_equations(const LinearStatement *st, Matrix *a, Matrix *b) {
    int n = st->dimension;
    vector_name = st->unknown[0].name;
    if (st->unknown[0].index >= 0) fail("il vettore incognito di un sistema è una lettera senza pedice");
    else if (linear_vector_degree(st->matrix_left) > 1 || linear_vector_degree(st->matrix_right) > 1) fail(LINEAR_SHAPE);
    Matrix x = matrix_zero(n, 1), origin = failure ? x : linear_residual(st, x);
    int m = origin.rows * origin.cols;
    if (!failure) {
        *a = matrix_new(m, n);
        *b = matrix_new(m, 1);
    }
    for (int i = 0; i < m && !failure; i++) *matrix_at(*b, i, 0) = frac_neg(origin.at[i]);
    for (int j = 0; j < n && !failure; j++) {
        *matrix_at(x, j, 0) = frac_int(1);
        Matrix there = linear_residual(st, x);
        *matrix_at(x, j, 0) = frac_int(0);
        for (int i = 0; i < m && !failure; i++) *matrix_at(*a, i, j) = frac_add(there.at[i], frac_neg(origin.at[i]));
    }
    vector_name = 0;
}

/* Mette in *point, una colonna, e in *directions il punto e i vettori
 * dell'insieme scritto di st, o del vettore di cui st parla:
 * l'elemento generico è point + (directions) (parametri). directions ha una
 * colonna per parametro, e non ha elementi se i parametri non ci sono.
 * Ricontrolla la lettura (vedi la testa del paragrafo). */
static void linear_stated(const LinearStatement *st, Matrix *point, Matrix *directions) {
    const VectorSum *sum = &st->stated;
    Frac at[MAX_UNKNOWNS];
    int n = sum->size, f = st->parameters;
    *point = matrix_new(n, 1);
    *directions = f ? matrix_new(n, f) : (Matrix){0, 0, NULL};
    for (int c = 0; c < n && !failure; c++) {
        LinearForm form;
        for (int i = 0; i <= f; i++) form.at[i] = frac_int(0);
        for (int t = 0; t < sum->terms && !failure; t++) {
            LinearForm entry = linear_form(sum->term[t].entry[c], st->parameter, f);
            if (sum->term[t].factor) entry = linear_times(linear_form(sum->term[t].factor, st->parameter, f), entry, f);
            form = linear_plus(form, entry, frac_int(sum->term[t].negative ? -1 : 1), f);
        }
        *matrix_at(*point, c, 0) = form.at[f];
        for (int j = 0; j < f; j++) *matrix_at(*directions, c, j) = form.at[j];

        /* Il ricontrollo: la componente com'è scritta, nei punti. */
        for (int which = 0; which <= f + 1 && !failure; which++) {
            Frac direct = frac_int(0);
            linear_sample(which, f, at);
            placed_letter = st->parameter;
            placed_value = at;
            placed_count = f;
            for (int t = 0; t < sum->terms; t++) {
                Frac value = matrix_number(sum->term[t].entry[c]);
                if (sum->term[t].factor) value = frac_mul(matrix_number(sum->term[t].factor), value);
                direct = frac_add(direct, sum->term[t].negative ? frac_neg(value) : value);
            }
            placed_count = 0;
            if (!failure && frac_cmp(direct, linear_at(&form, at, f)) != 0) linear_reading_failed();
        }
    }
}

/* 33b. L'ELIMINAZIONE, E I TESTIMONI CHE LASCIA
 *
 * Il sistema è A x = b, con A di m righe e n colonne. Si porta [A | b | I]
 * alla forma ridotta rispetto alle colonne di A (matrix_reduce(), 32b): le
 * operazioni sulle righe non cambiano le soluzioni, e lasciano [R | c | E],
 * dove R è la forma ridotta di A, E è il prodotto delle operazioni fatte
 * (E A = R) e c = E b. Siano r i perni, nelle colonne c_1 < ... < c_r.
 *
 * NESSUNA SOLUZIONE. Se una riga i dopo la r-esima, dove R è nulla, ha c_i
 * diverso da zero, l'equazione che quella riga dice è 0 = c_i. Il testimone
 * è la riga i di E, un vettore y: y A = 0 è la riga nulla di R, e y b = c_i.
 * Controllarlo è immediato, e non chiede altro: se A x = b avesse una
 * soluzione x, sarebbe 0 = (y A) x = y (A x) = y b, che non è zero. È la
 * combinazione delle equazioni, con i coefficienti y, che dà "0 = c_i". (Che
 * un sistema senza soluzioni abbia sempre un y così è l'alternativa di
 * Fredholm, e lo mostra l'eliminazione stessa; al controllo serve solo il
 * verso facile.)
 *
 * LE SOLUZIONI. Altrimenti le incognite delle colonne senza perno sono
 * libere, f = n - r, e la forma ridotta dà le altre:
 *
 *     x0, la soluzione con le incognite libere a zero: nel posto c_i ha c_i-esimo
 *         termine noto ridotto, cioè l'elemento i di c;
 *     V,  n righe e f colonne: la colonna di un'incognita libera j ha 1 nel
 *         posto j e, nel posto c_i, l'opposto dell'elemento (i, j) di R;
 *     G,  n righe e m colonne: la riga c_i è la riga i di E, le altre nulle;
 *     T,  f righe e n colonne: la riga di un'incognita libera j ha 1 nel
 *         posto j.
 *
 * Tre uguaglianze, che si controllano con dei prodotti, dicono che le
 * soluzioni sono esattamente i vettori x0 + V t:
 *
 *     (S1) A x0 = b:        x0 è una soluzione;
 *     (S2) A V = 0:         ogni x0 + V t è una soluzione, perché
 *                           A (x0 + V t) = A x0 + (A V) t = b;
 *     (S3) G A + V T = I:   ogni soluzione è di quella forma. Se A x = b,
 *                           z = x - x0 ha A z = 0, e allora
 *                           z = (G A + V T) z = G (A z) + V (T z) = V (T z):
 *                           x = x0 + V t con t = T z.
 *
 * Perché (S3) vale per le matrici costruite qui: G A ha nella riga c_i la
 * riga i di E A = R, che ha 1 nel posto c_i, 0 negli altri perni e gli
 * elementi di R nelle colonne libere; V T ha nella colonna di un'incognita
 * libera j la colonna di V, cioè 1 nella riga j e l'opposto di quegli
 * stessi elementi nelle righe c_i. Sommando restano gli 1 sulla diagonale.
 * Ma chi controlla non deve seguire questo ragionamento: moltiplica.
 *
 * Con f = 0 non ci sono V e T, e (S3) è G A = I: la soluzione è una sola. */

/* Che cosa l'eliminazione dice di un sistema A x = b (vedi qui sopra). Le
 * matrici che non servono non hanno elementi. */
typedef struct {
    int solvable;        /* 1 se il sistema ha soluzioni */
    Matrix combination;  /* senza soluzioni: y, 1 x m, con y A = 0 e y b diverso da zero */
    Matrix point;        /* con soluzioni: x0, n x 1 */
    int free;            /* con soluzioni: quante incognite sono libere, f */
    Matrix kernel;       /* con f > 0: V, n x f */
    Matrix left, pick;   /* con soluzioni: G, n x m; con f > 0: T, f x n */
} Solution;

/* Ritorna 1 se m è la matrice nulla. */
static int matrix_is_null(Matrix m) {
    for (int i = 0; i < m.rows * m.cols; i++)
        if (m.at[i].num != 0) return 0;
    return 1;
}

/* Ritorna 1 se G A + V T è l'identità, oppure G A da sola se V non ha
 * elementi: l'uguaglianza (S3). */
static int linear_spans(Matrix a, Matrix v, Matrix g, Matrix t) {
    int row, col;
    Matrix sum = matrix_mul(g, a);
    if (v.cols) sum = matrix_add(sum, matrix_mul(v, t), 0);
    return !failure && matrix_same(sum, matrix_identity(a.cols), &row, &col);
}

/* Risolve il sistema a x = b e ritorna ciò che l'eliminazione ne dice, con i
 * testimoni ricontrollati. */
static Solution linear_solve(Matrix a, Matrix b) {
    Solution s = {0, {0, 0, NULL}, {0, 0, NULL}, 0, {0, 0, NULL}, {0, 0, NULL}, {0, 0, NULL}};
    int m = a.rows, n = a.cols, row, col;

    /* [A | b | I], ridotta rispetto alle colonne di A. */
    Matrix all = matrix_new(m, n + 1 + m);
    for (int i = 0; i < all.rows; i++)
        for (int j = 0; j < all.cols; j++)
            *matrix_at(all, i, j) = j < n ? *matrix_at(a, i, j) : j == n ? *matrix_at(b, i, 0) : frac_int(j - n - 1 == i);
    int r = matrix_reduce(all, n);
    if (failure) return s;

    /* Nessuna soluzione: una riga 0 = c con c diverso da zero. */
    for (int i = r; i < m; i++) {
        if (matrix_at(all, i, n)->num == 0) continue;
        s.combination = matrix_new(1, m);
        for (int j = 0; j < s.combination.cols; j++) *matrix_at(s.combination, 0, j) = *matrix_at(all, i, n + 1 + j);
        if (!matrix_is_null(matrix_mul(s.combination, a)) || matrix_is_null(matrix_mul(s.combination, b))) matrix_witness_failed();
        return s;
    }

    /* Le soluzioni: x0 e G dalle righe dei perni, V e T dalle colonne libere. */
    s.free = n - r;
    s.point = matrix_zero(n, 1);
    s.left = matrix_zero(n, m);
    if (s.free) {
        s.kernel = matrix_zero(n, s.free);
        s.pick = matrix_zero(s.free, n);
    }
    if (failure) return s;
    for (int j = 0, i = 0, q = 0; j < n; j++) {
        if (i < r && matrix_at(all, i, j)->num != 0) {
            /* La colonna j ha il perno della riga i. */
            *matrix_at(s.point, j, 0) = *matrix_at(all, i, n);
            for (int k = 0; k < m; k++) *matrix_at(s.left, j, k) = *matrix_at(all, i, n + 1 + k);
            i++;
            continue;
        }

        /* La colonna j è libera: sopra di lei, nelle righe dei perni già
         * trovati, ci sono i suoi elementi nella forma ridotta; sotto, zeri.
         * Il perno della riga k sta nella colonna dove la riga comincia. */
        *matrix_at(s.kernel, j, q) = frac_int(1);
        *matrix_at(s.pick, q, j) = frac_int(1);
        for (int k = 0; k < i; k++) {
            int pivot = 0;
            while (matrix_at(all, k, pivot)->num == 0) pivot++;
            *matrix_at(s.kernel, pivot, q) = frac_neg(*matrix_at(all, k, j));
        }
        q++;
    }

    /* I controlli (S1), (S2), (S3), con soli prodotti. */
    if (!matrix_same(matrix_mul(a, s.point), b, &row, &col) || (s.free && !matrix_is_null(matrix_mul(a, s.kernel))) ||
        !linear_spans(a, s.kernel, s.left, s.pick)) matrix_witness_failed();
    s.solvable = !failure;
    return s;
}

/* 33c. CHE COSA DICE L'ENUNCIATO, E CHE COSA LO MOSTRA
 *
 * Con le soluzioni trovate (33b) ogni enunciato si decide, e ciò che lo
 * decide è di nuovo un testimone da moltiplicare. Il sistema è A x = b;
 * l'insieme scritto è p + U t, con U che può non avere colonne.
 *
 *   c1. "Il vettore p è una soluzione": si calcola A p e lo si confronta
 *       con b. Nessun testimone.
 *
 *   c2. "Non ci sono soluzioni". Vero: il vettore y di 33b. Falso: una
 *       soluzione, x0.
 *
 *   c3. "Le soluzioni sono p + U t". È vero quando valgono (S1), (S2) e
 *       (S3) per p e U al posto di x0 e V: lo dice lo stesso ragionamento di
 *       33b, che non usa nulla di particolare di x0 e di V. Le prime due si
 *       calcolano. Per la terza servono G e T, e si ricavano da quelli di
 *       33b: se ogni colonna di V è una combinazione delle colonne di U,
 *       V = U C, allora G A + U (C T) = G A + V T = I, e il testimone è G
 *       con C T. I coefficienti C si trovano risolvendo U c = v per ogni
 *       colonna v di V, un sistema come gli altri.
 *
 *       È falso in tre modi. Se A p non è b, o A U non è la matrice nulla,
 *       lo mostra il conto. Altrimenti una colonna v di V non è combinazione
 *       delle colonne di U, e allora z = p + v è una soluzione (A z = A p +
 *       A v = b) che l'insieme scritto non contiene: lo mostra il vettore y
 *       che 33b dà per il sistema U c = v, con y U = 0 e y v diverso da
 *       zero. Se z fosse p + U t, sarebbe y (z - p) = (y U) t = 0, e invece
 *       y (z - p) = y v. Se U non ha colonne basta che z sia diverso da p.
 *
 * Con x0 e V al posto di p e U, (c3) è la risposta di una richiesta. */

/* I modi in cui un enunciato su un sistema si decide (vedi qui sopra). I
 * primi quattro dicono che la cosa detta non vale: gli insiemi sono diversi,
 * o il vettore non è una soluzione. */
typedef enum {
    LINEAR_HAS_SOLUTIONS,    /* c2: detto impossibile, ma una soluzione c'è */
    LINEAR_POINT_FAILS,      /* c1, c3: il vettore scritto non è una soluzione */
    LINEAR_DIRECTION_FAILS,  /* c3: un vettore scritto non risolve il sistema omogeneo */
    LINEAR_OUTSIDE,          /* c3: c'è una soluzione che l'insieme scritto non contiene */
    LINEAR_NO_SOLUTIONS,     /* c2: è impossibile, come detto */
    LINEAR_POINT_SOLVES,     /* c1: il vettore scritto è una soluzione */
    LINEAR_EQUAL             /* c3: l'insieme scritto è quello delle soluzioni */
} LinearCause;

/* Che cosa mostra un enunciato vero o falso (vedi qui sopra): come si
 * decide, e i testimoni da scrivere nel certificato, nell'ordine. */
typedef struct {
    LinearCause cause;
    int witnesses;                /* testimoni validi: 0, 1 o 2 */
    const char *word[2];          /* il tipo di ognuno: "combination", "solution", "span" */
    Matrix first[2], second[2];   /* le sue matrici; second non ha elementi se è una sola */
    char note[512];               /* che cosa lo mostra, in italiano, per il verdetto */
} LinearEvidence;

/* Scrive in text, di size byte, il vettore colonna v come una tupla:
 * (1, -\frac{1}{2}, 0). È scritta in modo che 31s la rilegga uguale. */
static void linear_tuple(Matrix v, char *text, size_t size) {
    text_add(text, size, "(");
    for (int i = 0; i < v.rows; i++) {
        if (i) text_add(text, size, ", ");
        frac_latex(*matrix_at(v, i, 0), text, size);
    }
    text_add(text, size, ")");
}

/* Ritorna la colonna numero j della matrice m. */
static Matrix matrix_column(Matrix m, int j) {
    Matrix column = matrix_new(m.rows, 1);
    for (int i = 0; i < column.rows; i++) *matrix_at(column, i, 0) = *matrix_at(m, i, j);
    return column;
}

/* Aggiunge a e il testimone di tipo word con le matrici first e second
 * (second senza elementi se è una sola). */
static void linear_witness(LinearEvidence *e, const char *word, Matrix first, Matrix second) {
    e->word[e->witnesses] = word;
    e->first[e->witnesses] = first;
    e->second[e->witnesses++] = second;
}

/* Ritorna che cosa mostra l'enunciato st sul sistema a x = b, che ha le
 * soluzioni sol; point e directions sono il punto e i vettori dell'insieme
 * scritto, o il vettore di cui st parla (linear_stated()), e non contano se
 * l'insieme scritto è vuoto. */
static LinearEvidence linear_decide(const LinearStatement *st, Matrix a, Matrix b, Solution sol, Matrix point, Matrix directions) {
    static const Matrix none = {0, 0, NULL};
    LinearEvidence e = {LINEAR_POINT_FAILS, 0, {NULL, NULL}, {{0, 0, NULL}, {0, 0, NULL}}, {{0, 0, NULL}, {0, 0, NULL}}, ""};
    char tuple[256] = "";
    int row = 0, col = 0;
    if (failure) return e;

    /* c2. Il sistema detto impossibile. */
    if (st->empty) {
        e.cause = sol.solvable ? LINEAR_HAS_SOLUTIONS : LINEAR_NO_SOLUTIONS;
        if (sol.solvable) {
            linear_tuple(sol.point, tuple, sizeof tuple);
            snprintf(e.note, sizeof e.note, "il sistema ha soluzioni, per esempio %s", tuple);
            linear_witness(&e, "solution", sol.point, none);
        } else {
            snprintf(e.note, sizeof e.note, "il sistema non ha soluzioni");
            linear_witness(&e, "combination", sol.combination, none);
        }
        return e;
    }

    /* c1, e (S1) di c3: il punto scritto è una soluzione? */
    if (!matrix_same(matrix_mul(a, point), b, &row, &col)) {
        snprintf(e.note, sizeof e.note, "il vettore scritto non soddisfa l'equazione numero %d", row + 1);
        return e;
    }
    if (st->relation == LINEAR_IN || st->relation == LINEAR_NOTIN) {
        e.cause = LINEAR_POINT_SOLVES;
        snprintf(e.note, sizeof e.note, "il vettore scritto soddisfa tutte le equazioni");
        return e;
    }

    /* (S2): i vettori scritti risolvono il sistema omogeneo? */
    if (directions.cols && !matrix_is_null(matrix_mul(a, directions))) {
        e.cause = LINEAR_DIRECTION_FAILS;
        snprintf(e.note, sizeof e.note, "uno dei vettori che l'insieme scritto moltiplica per un parametro non risolve il sistema omogeneo");
        return e;
    }

    /* (S3): ogni colonna di V è combinazione delle colonne di U? C ha una
     * colonna di coefficienti per ogni colonna di V. */
    Matrix c = directions.cols && sol.free ? matrix_new(directions.cols, sol.free) : none;
    for (int j = 0; j < sol.free && !failure; j++) {
        Matrix v = matrix_column(sol.kernel, j);
        Solution inside = {0, {0, 0, NULL}, {0, 0, NULL}, 0, {0, 0, NULL}, {0, 0, NULL}, {0, 0, NULL}};
        if (directions.cols) inside = linear_solve(directions, v);
        if (failure) return e;
        if (inside.solvable) {
            for (int i = 0; i < c.rows; i++) *matrix_at(c, i, j) = *matrix_at(inside.point, i, 0);
            continue;
        }

        /* Una soluzione che l'insieme scritto non contiene. */
        Matrix z = matrix_add(point, v, 0);
        e.cause = LINEAR_OUTSIDE;
        linear_tuple(z, tuple, sizeof tuple);
        snprintf(e.note, sizeof e.note, "il sistema ha anche la soluzione %s, che l'insieme scritto non contiene", tuple);
        linear_witness(&e, "solution", z, none);
        if (directions.cols) linear_witness(&e, "combination", inside.combination, none);
        return e;
    }

    /* Sono uguali: G, e C T se ci sono vettori scritti. Senza incognite
     * libere C non c'è, e T è la matrice nulla: G A è già l'identità. */
    Matrix t = !directions.cols ? none : sol.free ? matrix_mul(c, sol.pick) : matrix_zero(directions.cols, a.cols);
    if (!failure && !linear_spans(a, directions, sol.left, t)) matrix_witness_failed();
    e.cause = LINEAR_EQUAL;
    snprintf(e.note, sizeof e.note, "l'insieme scritto è l'insieme delle soluzioni");
    linear_witness(&e, "span", sol.left, t);
    return e;
}

/* 33d. LA DIMOSTRAZIONE SCRITTA E IL CERTIFICATO
 *
 * Il certificato è l'enunciato, riscritto nella notazione del capitolo 17
 * di checker.c (17f), con la verità che il motore afferma e i testimoni di
 * 33c:
 *
 *     certificate matrices
 *     statement (= (solutions (matrix 2 3 1 1 1 3 3 -2) (matrix 2 1 1 2)) (affine (matrix 3 1 0 (/ 4 5) (/ 1 5)) (matrix 3 1 1 -1 0)))
 *     claim true
 *     witness span (matrix 3 2 ...) (matrix 1 3 ...)
 *     end
 *
 * (solutions A b) è l'insieme dei vettori x con A x = b; (affine p U) quello
 * dei vettori p + U t, e (affine p) il solo p; (nothing) l'insieme vuoto. Le
 * relazioni sono =, neq, in e notin. Del sistema il certificato scrive i
 * coefficienti letti, non le equazioni: come sono state lette è ciò che il
 * verificatore non ricontrolla, e che ricontrolla 33a.
 *
 * Warning: le parole e i testimoni sono quelli di ck_s_statement() (17f di
 * checker.c). Se ne aggiungi uno qui, aggiungilo là con il suo controllo. */

/* Aggiunge alla dimostrazione in corso la matrice m in LaTeX. */
static void linear_put(Matrix m) { matrix_put((MatrixValue){1, {0, 1}, m}); }

/* Scrive la dimostrazione di un enunciato sul sistema a x = b, in inglese
 * come le altre: il sistema, ciò che l'eliminazione ne dice (sol), poi ciò
 * che decide l'enunciato (e), con il punto e i vettori dell'insieme scritto
 * se c'è. truth dice se l'enunciato è vero. */
static void linear_proof(Matrix a, Matrix b, Solution sol, Matrix point, Matrix directions, const LinearEvidence *e, int truth) {
    /* Il sistema, e le sue soluzioni. */
    proof_add("Exact computation with rational numbers. In matrix form the system is $A x = b$ with $A = ");
    linear_put(a);
    proof_add("$ and $b = ");
    linear_put(b);
    proof_add("$. ");
    if (!sol.solvable) {
        proof_add("Gaussian elimination finds the combination of the equations with coefficients $y = ");
        linear_put(sol.combination);
        proof_add("$: it gives $y A = 0$ and $y b = ");
        linear_put(matrix_mul(sol.combination, b));
        proof_add("$, that is $0 = c$ with $c \\neq 0$, so the system has no solution. ");
    } else {
        proof_add("Gaussian elimination finds the solution $x_{0} = ");
        linear_put(sol.point);
        proof_add("$, checked by the product $A x_{0} = b$");
        if (sol.free) {
            proof_add(", and the matrix $V = ");
            linear_put(sol.kernel);
            proof_add("$ with $A V = 0$, so that every $x_{0} + V t$ is a solution. Conversely, with $G = ");
            linear_put(sol.left);
            proof_add("$ and $T = ");
            linear_put(sol.pick);
            proof_add("$ one has $G A + V T = I$: if $A x = b$ then $z = x - x_{0}$ satisfies $A z = 0$, hence $z = (G A + V T) z = V (T z)$. "
                      "The solutions are exactly the vectors $x_{0} + V t$. ");
        } else {
            proof_add(". With $G = ");
            linear_put(sol.left);
            proof_add("$ one has $G A = I$: if $A x = b$ then $x = G A x = G b$, so the solution is unique. ");
        }
    }

    /* Ciò che decide l'enunciato. */
    switch (e->cause) {
    case LINEAR_NO_SOLUTIONS: case LINEAR_HAS_SOLUTIONS:
        break;
    case LINEAR_POINT_FAILS: case LINEAR_POINT_SOLVES:
        proof_add("For the stated vector $p = ");
        linear_put(point);
        proof_add("$ the product is $A p = ");
        linear_put(matrix_mul(a, point));
        proof_add(e->cause == LINEAR_POINT_SOLVES ? "$, which is $b$. " : "$, which is not $b$: $p$ is not a solution. ");
        break;
    case LINEAR_DIRECTION_FAILS:
        proof_add("For the stated directions $U = ");
        linear_put(directions);
        proof_add("$ the product is $A U = ");
        linear_put(matrix_mul(a, directions));
        proof_add("$, which is not zero: a stated vector is not a solution. ");
        break;
    case LINEAR_OUTSIDE:
        proof_add("The vector $z = ");
        linear_put(e->first[0]);
        proof_add("$ is a solution, $A z = b$, and the stated set does not contain it");
        if (e->witnesses > 1) {
            proof_add(": the row $y = ");
            linear_put(e->first[1]);
            proof_add("$ gives $y U = 0$ on the stated directions $U$ and $y (z - p) \\neq 0$ for the stated point $p$");
        }
        proof_add(". ");
        break;
    case LINEAR_EQUAL:
        proof_add("For the stated set, with the point $p = ");
        linear_put(point);
        if (directions.cols) {
            proof_add("$ and the directions $U = ");
            linear_put(directions);
            proof_add("$: $A p = b$, $A U = 0$, and $G A + U T' = I$ with $T' = ");
            linear_put(e->second[0]);
            proof_add("$. As above, the solutions are exactly the vectors $p + U t$. ");
        } else {
            proof_add("$: $A p = b$, and the solution is unique. ");
        }
        break;
    }
    proof_add(truth ? "Hence the stated relation holds." : "Hence the stated relation does not hold.");
}

/* Scrive in certificate_text il certificato dell'enunciato st sul sistema
 * a x = b, con l'insieme scritto point + directions t (se non è vuoto), la
 * verità truth e i testimoni di e. */
static void linear_certificate(const LinearStatement *st, Matrix a, Matrix b, Matrix point, Matrix directions, const LinearEvidence *e, int truth) {
    int member = st->relation == LINEAR_IN || st->relation == LINEAR_NOTIN;
    certificate_length = 0;
    certificate_broken = 0;
    cert_add("certificate matrices\nstatement (%s", st->relation == LINEAR_EQ ? "=" : st->relation == LINEAR_NEQ ? "neq" : st->relation == LINEAR_IN ? "in" : "notin");
    if (member) matrix_cert_table(point);
    cert_add(" (solutions");
    matrix_cert_table(a);
    matrix_cert_table(b);
    cert_add(")");
    if (st->empty) cert_add(" (nothing)");
    else if (!member) {
        cert_add(" (affine");
        matrix_cert_table(point);
        if (directions.cols) matrix_cert_table(directions);
        cert_add(")");
    }
    cert_add(")\nclaim %s\n", truth ? "true" : "false");
    for (int w = 0; w < e->witnesses; w++) {
        cert_add("witness %s", e->word[w]);
        matrix_cert_table(e->first[w]);
        if (e->second[w].cols) matrix_cert_table(e->second[w]);
        cert_add("\n");
    }
    cert_add("end\n");
}

/* 33e. UN ENUNCIATO DECISO: LE SOLUZIONI SCRITTE, IL SÌ DEL VERIFICATORE */

/* Scrive in text, di size byte, l'insieme delle soluzioni sol come nei
 * libri: \emptyset, \{(1, 2)\}, oppure una soluzione particolare più i
 * parametri liberi, \{(1, 0) + t (2, 1) \mid t \in \mathbb{R}\}. La soluzione
 * particolare nulla non si scrive, se ci sono parametri. Le lettere dei
 * parametri sono le prime di un elenco che non sono già incognite di st né
 * lettere a cui l'enunciato ha dato un valore. Il testo è scritto in modo
 * che 31s lo rilegga. */
static void linear_answer(const LinearStatement *st, Solution sol, char *text, size_t size) {
    static const char names[] = "tsuvwpqrabcdfghjklmnxyz";
    char letter[MAX_UNKNOWNS];
    if (!sol.solvable) { text_add(text, size, "\\emptyset"); return; }

    /* Le lettere dei parametri. */
    int found = 0;
    for (const char *p = names; *p && found < sol.free; p++) {
        int taken = 0;
        for (int i = 0; i < st->unknowns; i++) taken |= st->unknown[i].name == *p;
        for (int i = 0; i < letter_count; i++) taken |= letter_name[i] == *p;
        if (!taken) letter[found++] = *p;
    }
    if (found < sol.free) { fail("non ci sono abbastanza lettere per i parametri delle soluzioni"); return; }

    /* Il punto, poi un addendo per parametro. */
    text_add(text, size, "\\{");
    if (!sol.free || !matrix_is_null(sol.point)) linear_tuple(sol.point, text, size);
    for (int j = 0; j < sol.free; j++) {
        text_add(text, size, "%s%c ", j || !matrix_is_null(sol.point) ? " + " : "", letter[j]);
        linear_tuple(matrix_column(sol.kernel, j), text, size);
    }
    for (int j = 0; j < sol.free; j++) text_add(text, size, "%s%c", j ? ", " : " \\mid ", letter[j]);
    text_add(text, size, sol.free ? " \\in \\mathbb{R}\\}" : "\\}");
}

/* Legge il sistema di st in *a e *b (33a) e lo risolve (33b), con i valori
 * che le lettere dell'enunciato hanno in questo momento. Prima calcola le
 * definizioni di names, come nel capitolo 32: ognuna deve avere un valore. */
static Solution linear_solution(const LinearStatement *st, const MatrixStatement *names, Matrix *a, Matrix *b) {
    static const Matrix none = {0, 0, NULL};
    *a = *b = none;
    for (int i = 0; i < names->definitions && !failure; i++) matrix_eval(names->definition[i], 0);
    if (!failure) {
        if (st->vector) linear_vector_equations(st, a, b);
        else linear_equations(st, a, b);
    }
    return failure ? (Solution){0, none, none, 0, none, none, none} : linear_solve(*a, *b);
}

/* Decide l'enunciato st, che non è una richiesta, con i valori che le
 * lettere hanno in questo momento: mette in *truth se è vero e in *e ciò
 * che lo mostra, aggiunge la sua dimostrazione a quella in corso, e scrive
 * in certificate_text il certificato, che fa controllare al verificatore.
 * Ritorna NULL se il verificatore lo accetta. Altrimenti ritorna il motivo,
 * e *outcome dice se l'enunciato è fuori dal linguaggio (UNSUPPORTED) o se è
 * il certificato a non essere stato accettato (NOT_PROVED). */
static const char *linear_settle(const LinearStatement *st, const MatrixStatement *names, int *truth, LinearEvidence *e, Outcome *outcome) {
    static _Thread_local char problem[512];
    Matrix a, b, point = {0, 0, NULL}, directions = point;
    *outcome = UNSUPPORTED;
    Solution sol = linear_solution(st, names, &a, &b);

    /* L'insieme scritto, o il vettore: deve stare nello spazio delle
     * incognite. Poi che cosa l'enunciato dice, e che cosa lo mostra. */
    if (!failure && !st->empty) {
        if (st->stated.size != st->dimension) fail("i vettori scritti non hanno tante componenti quante sono le incognite del sistema");
        else linear_stated(st, &point, &directions);
    }
    *e = linear_decide(st, a, b, sol, point, directions);
    if (failure) return failure;
    *truth = (st->relation == LINEAR_EQ || st->relation == LINEAR_IN) == (e->cause >= LINEAR_NO_SOLUTIONS);

    /* La dimostrazione scritta. */
    linear_proof(a, b, sol, point, directions, e, *truth);
    if (failure || proof_broken) return failure ? failure : "dimostrazione troppo lunga da scrivere";

    /* Il certificato, e la risposta del verificatore (vedi "Il controllo
     * indipendente" in testa al capitolo). */
    const char *why = "il certificato non si può scrivere", *text = certificate_text;
    linear_certificate(st, a, b, point, directions, e, *truth);
    CkAnswer checked = certificate_broken ? CK_UNSUPPORTED : ck_check(&text, &why, checker_steps());
    if (checked == CK_ACCEPTED) return NULL;
    if (checked == CK_REJECTED) unjustified_steps++;
    *outcome = NOT_PROVED;
    snprintf(problem, sizeof problem, checked == CK_REJECTED ? "il verificatore indipendente ha respinto il certificato: %s"
                                                             : "il verificatore non sa controllare il certificato: %s", why);
    return problem;
}

/* 33f. POLINOMI IN UNA LETTERA, E MATRICI DI POLINOMI
 *
 * A che cosa servono. Con un parametro k nei coefficienti, il rango di una
 * matrice e le soluzioni di un sistema non sono più numeri: fuori da pochi
 * valori di k sono dati da formule in k, e in quei valori cambiano. Le
 * formule sono polinomi in k, o frazioni di polinomi con lo stesso
 * denominatore (33g): per scriverle, e per ricontrollarle prima di darle al
 * verificatore, servono somme e prodotti di polinomi in una lettera sola a
 * coefficienti razionali. Sono polinomi piccoli (i gradi sono quelli di un
 * determinante 4 x 4 con elementi di primo o secondo grado), e stanno in un
 * vettore di lunghezza fissa. */

#define MAX_UPOLY 40    /* coefficienti di un polinomio in una lettera: il grado arriva a MAX_UPOLY - 1 */
#define MAX_GENERIC 6   /* ordine del minore di una matrice con un parametro: il suo determinante si sviluppa con Laplace */

/* Un polinomio in una lettera a coefficienti razionali: at[i] è il
 * coefficiente della potenza i. Invariante: degree è il grado, at[degree]
 * non è zero; il polinomio nullo ha degree uguale a -1. */
typedef struct {
    int degree;
    Frac at[MAX_UPOLY];
} UPoly;

/* Ritorna il polinomio costante c. */
static UPoly up_number(Frac c) {
    UPoly p;
    p.degree = c.num ? 0 : -1;
    p.at[0] = c;
    return p;
}

/* Ritorna la somma a + sign b, con sign uguale a 1 o a -1. */
static UPoly up_add(UPoly a, UPoly b, int sign) {
    UPoly r;
    r.degree = a.degree > b.degree ? a.degree : b.degree;
    for (int i = 0; i <= r.degree; i++) {
        Frac x = i <= a.degree ? a.at[i] : frac_int(0), y = i <= b.degree ? b.at[i] : frac_int(0);
        r.at[i] = frac_add(x, sign < 0 ? frac_neg(y) : y);
    }
    while (r.degree >= 0 && r.at[r.degree].num == 0) r.degree--;
    return r;
}

/* Ritorna il prodotto a b. Annota un errore se il grado non sta nel vettore. */
static UPoly up_mul(UPoly a, UPoly b) {
    UPoly r;
    r.degree = -1;
    if (failure || a.degree < 0 || b.degree < 0) return r;
    if (a.degree + b.degree >= MAX_UPOLY) { fail("con un parametro i polinomi che servono hanno un grado troppo alto"); return r; }
    r.degree = a.degree + b.degree;
    for (int i = 0; i <= r.degree; i++) r.at[i] = frac_int(0);
    for (int i = 0; i <= a.degree; i++)
        for (int j = 0; j <= b.degree; j++) r.at[i + j] = frac_add(r.at[i + j], frac_mul(a.at[i], b.at[j]));
    return r;
}

/* Ritorna il valore di p nel punto x, con lo schema di Horner. */
static Frac up_at(const UPoly *p, Frac x) {
    Frac value = frac_int(0);
    for (int i = p->degree; i >= 0; i--) value = frac_add(frac_mul(value, x), p->at[i]);
    return value;
}

/* Ritorna 1 se a e b sono lo stesso polinomio. */
static int up_same(const UPoly *a, const UPoly *b) {
    if (a->degree != b->degree) return 0;
    for (int i = 0; i <= a->degree; i++)
        if (frac_cmp(a->at[i], b->at[i]) != 0) return 0;
    return 1;
}

/* Divide a per b, che non è nullo: mette in *quotient il quoziente e ritorna
 * il resto. È la divisione dei libri: finché il resto ha grado non minore di
 * b, gli si toglie il multiplo di b che ne cancella il termine di grado più
 * alto. */
static UPoly up_divide(UPoly a, UPoly b, UPoly *quotient) {
    quotient->degree = a.degree - b.degree;
    for (int i = 0; i <= quotient->degree; i++) quotient->at[i] = frac_int(0);
    while (a.degree >= b.degree && !failure) {
        int shift = a.degree - b.degree;
        Frac c = frac_div(a.at[a.degree], b.at[b.degree]);
        quotient->at[shift] = c;
        for (int i = 0; i <= b.degree; i++) a.at[i + shift] = frac_add(a.at[i + shift], frac_neg(frac_mul(c, b.at[i])));
        a.degree--;
        while (a.degree >= 0 && a.at[a.degree].num == 0) a.degree--;
    }
    if (quotient->degree < 0) quotient->degree = -1;
    return a;
}

/* Ritorna il massimo comun divisore di a e b con l'algoritmo di Euclide,
 * reso monico (coefficiente del grado più alto uguale a 1); se sono tutti e
 * due nulli ritorna il polinomio nullo. */
static UPoly up_gcd(UPoly a, UPoly b) {
    UPoly quotient;
    while (b.degree >= 0 && !failure) {
        UPoly rest = up_divide(a, b, &quotient);
        a = b;
        b = rest;
    }
    if (a.degree >= 0) {
        Frac lead = a.at[a.degree];
        for (int i = 0; i <= a.degree; i++) a.at[i] = frac_div(a.at[i], lead);
    }
    return a;
}

/* Ritorna il polinomio di grado minore di count che nei punti x[0], ...,
 * x[count - 1], tutti diversi, vale y[0], ..., y[count - 1]: è unico, perché
 * la differenza di due così avrebbe count radici e grado minore di count.
 *
 * Con le differenze divise di Newton: il polinomio è
 * c_0 + c_1 (X - x_0) + c_2 (X - x_0)(X - x_1) + ..., dove c_j è la
 * differenza divisa dei primi j + 1 punti, calcolata sul posto; poi i
 * prodotti si svolgono dall'ultimo, P diventa P (X - x_j) + c_j. count è al
 * più MAX_UPOLY. */
static UPoly up_interpolate(const Frac *x, const Frac *y, int count) {
    Frac c[MAX_UPOLY];
    UPoly p = up_number(frac_int(0)), factor;
    for (int i = 0; i < count; i++) c[i] = y[i];
    for (int k = 1; k < count; k++)
        for (int j = count - 1; j >= k; j--) c[j] = frac_div(frac_add(c[j], frac_neg(c[j - 1])), frac_add(x[j], frac_neg(x[j - k])));
    factor.degree = 1;
    factor.at[1] = frac_int(1);
    for (int j = count - 1; j >= 0 && !failure; j--) {
        factor.at[0] = frac_neg(x[j]);
        p = up_add(up_mul(p, factor), up_number(c[j]), 1);
    }
    return p;
}

/* Aggiunge a text, di size byte, il polinomio p nella lettera letter, in
 * LaTeX, dai gradi più alti: k^{2} - 14 k + 45. È scritto in modo che il
 * capitolo 9 lo rilegga uguale. */
static void up_latex(const UPoly *p, int letter, char *text, size_t size) {
    size_t start = strlen(text);
    char body[32];
    for (int i = p->degree; i >= 0 && !failure; i--) {
        if (i == 0) body[0] = 0;
        else if (i == 1) snprintf(body, sizeof body, "%c", letter);
        else snprintf(body, sizeof body, "%c^{%d}", letter, i);
        term_latex(p->at[i], body, text + start, size - start);
    }
    if (!text[start]) text_add(text, size, "0");
}

/* Scrive nel certificato in corso il polinomio p nella lettera letter, come
 * somma dei suoi termini: (+ (+ 45 (* -14 k)) (^ k 2)). */
static void cert_upoly(const UPoly *p, int letter) {
    int terms = 0, written = 0;
    for (int i = 0; i <= p->degree; i++) terms += p->at[i].num != 0;
    if (!terms) cert_add("0");
    for (int i = 1; i < terms; i++) cert_add("(+ ");
    for (int i = 0; i <= p->degree; i++) {
        if (p->at[i].num == 0) continue;
        if (written++) cert_add(" ");
        if (i == 0) cert_frac(p->at[i]);
        else {
            int one = p->at[i].num == 1 && p->at[i].den == 1;
            if (!one) { cert_add("(* "); cert_frac(p->at[i]); cert_add(" "); }
            cert_add(i == 1 ? "%c" : "(^ %c %d)", letter, i);
            if (!one) cert_add(")");
        }
        if (written > 1) cert_add(")");
    }
}

/* Mette in root[], lungo max, le radici razionali distinte di p, che non è
 * il polinomio nullo, in ordine crescente, e ne ritorna il numero; annota un
 * errore se sono più di max o se i coefficienti sono troppo grandi.
 *
 * Con il teorema delle radici razionali. Moltiplicato p per un intero che ne
 * toglie i denominatori, e tolte le potenze della lettera che lo dividono
 * (la radice zero), resta a_n X^n + ... + a_0 con coefficienti interi e a_0
 * diverso da zero. Se la frazione ridotta u/v ne è una radice, moltiplicando
 * per v^n si ha a_n u^n + a_{n-1} u^{n-1} v + ... + a_0 v^n = 0: u divide
 * l'ultimo addendo, e quindi a_0, perché non ha fattori in comune con v; e
 * v divide il primo, e quindi a_n. I candidati sono finiti, e si provano
 * tutti: è un conto completo, non una ricerca a tentativi. Che le radici
 * reali siano poi solo queste lo dice un altro conto (33h). */
static int up_rational_roots(UPoly p, Frac *root, int max) {
    const long long limit = 1000000000000LL;
    int count = 0, low = 0;
    __int128 scale = 1;
    if (failure || p.degree < 1) return 0;

    /* Coefficienti interi, e la radice zero. */
    for (int i = 0; i <= p.degree; i++) {
        scale = scale / gcd128(scale, p.at[i].den) * p.at[i].den;
        if (scale > limit) { fail("coefficienti troppo grandi per cercare i valori speciali del parametro"); return 0; }
    }
    for (int i = 0; i <= p.degree; i++) p.at[i] = frac_mul(p.at[i], frac_make(scale, 1));

    /* Va guardato prima di cercare il primo coefficiente non nullo: un
     * prodotto troppo grande lascia uno zero al suo posto, anche nel
     * coefficiente direttivo, e la ricerca uscirebbe dal polinomio. */
    if (failure) return 0;
    while (p.at[low].num == 0) low++;
    if (low) root[count++] = frac_int(0);
    long long first = p.at[low].num < 0 ? -p.at[low].num : p.at[low].num, last = p.at[p.degree].num < 0 ? -p.at[p.degree].num : p.at[p.degree].num;
    if (failure || first > limit || last > limit) { fail("coefficienti troppo grandi per cercare i valori speciali del parametro"); return 0; }

    /* I candidati u / v e -u / v, con u che divide il termine noto e v il
     * coefficiente direttivo. Di ogni coppia di divisori complementari
     * basta trovare il più piccolo. */
    for (long long u0 = 1; u0 * u0 <= first && !failure; u0++) {
        if (first % u0) continue;
        for (int pass = 0; pass < 2; pass++) {
            long long u = pass ? first / u0 : u0;
            if (pass && u == u0) continue;
            for (long long v0 = 1; v0 * v0 <= last && !failure; v0++) {
                if (last % v0) continue;
                for (int half = 0; half < 2; half++) {
                    long long v = half ? last / v0 : v0;
                    if ((half && v == v0) || gcd128(u, v) != 1) continue;
                    for (int sign = 1; sign >= -1 && !failure; sign -= 2) {
                        Frac x = frac_make(sign * u, v);
                        if (up_at(&p, x).num != 0 || failure) continue;
                        if (count == max) { fail("troppi valori speciali del parametro"); return 0; }
                        root[count++] = x;
                    }
                }
            }
        }
    }

    /* In ordine crescente. */
    for (int i = 1; i < count; i++)
        for (int j = i; j > 0 && frac_cmp(root[j - 1], root[j]) > 0; j--) {
            Frac swap = root[j];
            root[j] = root[j - 1];
            root[j - 1] = swap;
        }
    return failure ? 0 : count;
}

/* Una matrice di polinomi in una lettera: rows righe e cols colonne, con gli
 * elementi per righe in at[], nell'arena. Con rows e cols a zero non ha
 * elementi: è il risultato di un conto fallito, o una matrice che non c'è. */
typedef struct {
    int rows, cols;
    UPoly *at;
} PMatrix;

static const PMatrix NO_PMATRIX = {0, 0, NULL};

/* Ritorna la matrice rows x cols di polinomi nulli. Le due dimensioni sono
 * almeno 1. */
static PMatrix pm_new(int rows, int cols) {
    PMatrix m = NO_PMATRIX;
    if (failure) return m;
    m.at = arena_alloc((size_t)rows * (size_t)cols * sizeof(UPoly));
    if (!m.at) return m;
    m.rows = rows;
    m.cols = cols;
    for (int i = 0; i < rows * cols; i++) m.at[i].degree = -1;
    return m;
}

/* Ritorna l'indirizzo dell'elemento di m nella riga i e colonna j, da zero. */
static UPoly *pm_at(PMatrix m, int i, int j) { return &m.at[(size_t)i * (size_t)m.cols + (size_t)j]; }

/* Ritorna il prodotto righe per colonne a b; le colonne di a sono quante le
 * righe di b. */
static PMatrix pm_mul(PMatrix a, PMatrix b) {
    PMatrix r = pm_new(a.rows, b.cols);
    if (!matrix_spend((long long)r.rows * r.cols * a.cols)) return NO_PMATRIX;
    for (int i = 0; i < r.rows; i++)
        for (int j = 0; j < r.cols; j++)
            for (int k = 0; k < a.cols && !failure; k++) *pm_at(r, i, j) = up_add(*pm_at(r, i, j), up_mul(*pm_at(a, i, k), *pm_at(b, k, j)), 1);
    return failure ? NO_PMATRIX : r;
}

/* Ritorna a + sign b, con sign uguale a 1 o a -1; le due matrici hanno le
 * stesse dimensioni. */
static PMatrix pm_add(PMatrix a, PMatrix b, int sign) {
    PMatrix r = pm_new(a.rows, a.cols);
    for (int i = 0; i < r.rows * r.cols; i++) r.at[i] = up_add(a.at[i], b.at[i], sign);
    return r;
}

/* Ritorna c m: ogni elemento di m moltiplicato per il polinomio c. */
static PMatrix pm_scale(PMatrix m, UPoly c) {
    PMatrix r = pm_new(m.rows, m.cols);
    for (int i = 0; i < r.rows * r.cols && !failure; i++) r.at[i] = up_mul(c, m.at[i]);
    return failure ? NO_PMATRIX : r;
}

/* Ritorna 1 se a e b hanno le stesse dimensioni e gli stessi polinomi. */
static int pm_same(PMatrix a, PMatrix b) {
    if (failure || a.rows != b.rows || a.cols != b.cols) return 0;
    for (int i = 0; i < a.rows * a.cols; i++)
        if (!up_same(&a.at[i], &b.at[i])) return 0;
    return 1;
}

/* Ritorna il primo posto di m, per righe, in cui c'è un polinomio non
 * nullo; -1 se m è la matrice nulla. */
static int pm_first(PMatrix m) {
    for (int i = 0; i < m.rows * m.cols; i++)
        if (m.at[i].degree >= 0) return i;
    return -1;
}

/* Ritorna la matrice n x n con il polinomio c sulla diagonale. */
static PMatrix pm_diagonal(int n, UPoly c) {
    PMatrix m = pm_new(n, n);
    for (int i = 0; i < m.rows; i++) *pm_at(m, i, i) = c;
    return m;
}

/* Ritorna la matrice di numeri che m vale quando la lettera vale x. */
static Matrix pm_value(PMatrix m, Frac x) {
    Matrix r = matrix_new(m.rows, m.cols);
    for (int i = 0; i < r.rows * r.cols; i++) r.at[i] = up_at(&m.at[i], x);
    return r;
}

/* Ritorna la matrice fatta delle righe row[0], ..., row[rows - 1] e delle
 * colonne col[0], ..., col[cols - 1] di m. Con row o col a NULL prende
 * tutte le righe, o tutte le colonne, e il conto accanto non conta. */
static PMatrix pm_pick(PMatrix m, const int *row, int rows, const int *col, int cols) {
    PMatrix r = pm_new(row ? rows : m.rows, col ? cols : m.cols);
    for (int i = 0; i < r.rows; i++)
        for (int j = 0; j < r.cols; j++) *pm_at(r, i, j) = *pm_at(m, row ? row[i] : i, col ? col[j] : j);
    return r;
}

/* Ritorna la matrice m senza la riga i e la colonna j; m ha almeno due
 * righe e due colonne. */
static PMatrix pm_without(PMatrix m, int i, int j) {
    PMatrix r = pm_new(m.rows - 1, m.cols - 1);
    for (int a = 0; a < r.rows; a++)
        for (int b = 0; b < r.cols; b++) *pm_at(r, a, b) = *pm_at(m, a + (a >= i), b + (b >= j));
    return r;
}

/* Ritorna il determinante della matrice quadrata m, con lo sviluppo di
 * Laplace lungo la prima riga: la somma, a segni alterni, di ogni elemento
 * della riga per il determinante di ciò che resta tolte la sua riga e la sua
 * colonna. Con i polinomi non si può dividere per un perno, che per qualche
 * valore della lettera si annulla; le matrici sono piccole (MAX_GENERIC), e
 * lo sviluppo basta. */
static UPoly pm_det(PMatrix m) {
    UPoly sum = up_number(frac_int(0));
    if (failure || !matrix_spend(m.rows)) return sum;
    if (m.rows == 1) return m.at[0];
    for (int j = 0; j < m.cols && !failure; j++) {
        /* La sottomatrice serve solo per questo addendo: la sua memoria si
         * restituisce, il determinante è un valore. */
        size_t mark = arena_used;
        if (pm_at(m, 0, j)->degree < 0) continue;
        sum = up_add(sum, up_mul(*pm_at(m, 0, j), pm_det(pm_without(m, 0, j))), j % 2 ? -1 : 1);
        arena_used = mark;
    }
    return sum;
}

/* Ritorna l'aggiunta della matrice quadrata m: nel posto (j, i) il
 * determinante di m senza la riga i e la colonna j, con il segno (-1)^(i+j).
 * Vale m adj(m) = adj(m) m = det(m) I (lo sviluppo di Laplace, letto riga
 * per riga): dove il determinante non è zero, adj(m) / det(m) è l'inversa.
 * Di una matrice 1 x 1 è la matrice (1). */
static PMatrix pm_adjugate(PMatrix m) {
    PMatrix r = pm_new(m.rows, m.rows);
    for (int i = 0; i < r.rows && !failure; i++)
        for (int j = 0; j < r.rows && !failure; j++) {
            size_t mark = arena_used;
            UPoly minor = m.rows == 1 ? up_number(frac_int(1)) : pm_det(pm_without(m, i, j));
            *pm_at(r, j, i) = (i + j) % 2 ? up_add(up_number(frac_int(0)), minor, -1) : minor;
            arena_used = mark;
        }
    return failure ? NO_PMATRIX : r;
}

/* Scrive nel certificato in corso, preceduta da uno spazio, la matrice di
 * polinomi m nella lettera letter. */
static void cert_pmatrix(PMatrix m, int letter) {
    cert_add(" (matrix %d %d", m.rows, m.cols);
    for (int i = 0; i < m.rows * m.cols; i++) {
        cert_add(" ");
        cert_upoly(&m.at[i], letter);
    }
    cert_add(")");
}

/* Scrive nel certificato in corso, preceduta da uno spazio, la matrice
 * (above / below) m: i polinomi di m moltiplicati per above e divisi per
 * below. Se above e below sono tutti e due il numero 1 scrive m da sola. */
static void cert_pmatrix_over(PMatrix m, const UPoly *above, const UPoly *below, int letter) {
    UPoly one = up_number(frac_int(1));
    if (up_same(above, &one) && up_same(below, &one)) { cert_pmatrix(m, letter); return; }
    cert_add(" (* (/ ");
    cert_upoly(above, letter);
    cert_add(" ");
    cert_upoly(below, letter);
    cert_add(")");
    cert_pmatrix(m, letter);
    cert_add(")");
}

/* 33g. CON UN PARAMETRO: IL CASO GENERICO
 *
 * A che cosa serve. "Discutere il sistema al variare di k", "calcolare il
 * rango al variare di k": è l'esercizio più frequente dei libri di algebra
 * lineare. La risposta è un elenco di casi: per quasi tutti i valori di k
 * vale una sola formula (il caso generico), e in pochi valori speciali la
 * risposta è un'altra. Qui si trova il caso generico, con il polinomio che
 * dice dove vale; i valori speciali sono le sue radici, e in ognuno il conto
 * è quello sui numeri delle sezioni precedenti (33h).
 *
 * IL RANGO GENERICO. Sia A una matrice con gli elementi polinomi in k. Si
 * dà a k un valore qualsiasi k0 e si prendono, dalla matrice di numeri
 * A(k0), r righe e r colonne che ne dicono il rango: le colonne dei perni
 * della sua forma ridotta, e quelle della sua trasposta. Il minore M di A
 * fatto di quelle righe R e di quelle colonne C ha il determinante d(k), un
 * polinomio che in k0 non si annulla: quindi non è il polinomio nullo. Con
 * l'aggiunta adj(M), per cui M adj(M) = adj(M) M = d I:
 *
 *   (G1) dove d(k) non è zero il rango è almeno r, perché M è invertibile;
 *   (G2) se vale l'uguaglianza tra matrici di polinomi
 *
 *            d A = A[:, C] adj(M) A[R, :]
 *
 *        (le colonne C di A, per l'aggiunta, per le righe R di A), allora
 *        dove d(k) non è zero A = A[:, C] (adj(M) / d) A[R, :] è il prodotto
 *        di una matrice con r colonne per una con r righe, e il rango è al
 *        più r.
 *
 * (G2) si controlla moltiplicando. Se non vale, k0 era un valore speciale,
 * e si prova il successivo: i valori in cui il rango è più basso di quello
 * generico sono finiti, perché annullano un polinomio non nullo. Quando
 * vale, r è il rango per ogni k fuori dalle radici di d: è il caso generico,
 * e d è il polinomio che lo delimita. I testimoni per il verificatore (17b,
 * con le lettere) sono C = A[:, C], F = adj(M) A[R, :] / d, G con adj(M) / d
 * nelle colonne R, H che sceglie le colonne C.
 *
 * IL SISTEMA GENERICO. Per A x = b, con lo stesso minore:
 *
 *   - il residuo della riga i, d b_i - A[i, C] adj(M) b[R], è un polinomio.
 *     Se per una riga non è nullo, la combinazione y delle equazioni che ha
 *     d nel posto i e -A[i, C] adj(M) nei posti R dà y A = 0 (per (G2), riga
 *     i) e y b = quel residuo: dove il residuo non è zero il sistema è
 *     impossibile (33b);
 *   - se tutti i residui sono nulli, le formule di Cramer danno le soluzioni
 *     dove d non è zero: x0 = N / d con N = adj(M) b[R] nei posti C e zero
 *     altrove; per ogni colonna libera j il vettore con d nel posto j e
 *     -adj(M) A[R, j] nei posti C; G con adj(M) / d nelle righe C e nelle
 *     colonne R; T che sceglie le incognite libere, diviso per d. Le tre
 *     uguaglianze (S1), (S2), (S3) di 33b diventano uguaglianze tra matrici
 *     di polinomi, A N = d b, A V = 0, G A + V T = d I, e si controllano
 *     moltiplicando, qui e poi nel verificatore.
 *
 * L'INSIEME SCRITTO CON IL PARAMETRO. Un insieme scritto p + U t può avere
 * il parametro k nelle componenti, anche a denominatore: \frac{k + 1}{k -
 * 2}. Le sue componenti sono frazioni di polinomi in k, e si trovano così:
 * mult è il prodotto di tutti i divisori scritti che contengono k; una
 * componente moltiplicata per mult è un polinomio, di cui si sa limitare il
 * grado dalla scrittura, e un polinomio è determinato dai suoi valori in
 * abbastanza punti (up_interpolate()), che sono il conto di 33a con un
 * numero al posto di k. Così p = NP / mult e U = NU / mult. L'insieme
 * scritto è quello delle soluzioni, dove un certo polinomio non si annulla,
 * quando A NP = mult b, A NU = 0 e i suoi vettori sono tanti quante le
 * incognite libere e indipendenti: la matrice Q che ne prende le componenti
 * libere ha il determinante non nullo, e allora (33c, c3) il testimone è G
 * con T' = Q^{-1} T, perché U Q^{-1} sono i vettori V di qui sopra (ogni
 * vettore v del nucleo è V per le sue componenti libere).
 *
 * Che cosa resta fuori, e il verdetto lo dice: più di un parametro; un
 * parametro a denominatore nei coefficienti del sistema, o dentro una radice
 * o una funzione; un insieme scritto con più vettori delle incognite libere;
 * un valore speciale irrazionale (33h); matrici con più di MAX_GENERIC righe
 * indipendenti.
 */

#define MAX_PARAMETER_SIDE 16  /* righe, o colonne, di una matrice con un parametro */
#define GENERIC_SAMPLES 64     /* valori del parametro provati per trovarne uno generico */
#define MAX_SPECIAL 12         /* valori speciali del parametro in una discussione */

static const char *const PARAMETER_SHAPE =
    "con un parametro i coefficienti di un sistema e gli elementi di una matrice sono polinomi nel parametro, e un insieme scritto ha il parametro "
    "solo in polinomi e in frazioni di polinomi: niente radici o funzioni del parametro";
static const char *const PARAMETER_SIZE = "matrice troppo grande per la discussione con un parametro";

/* Ritorna un limite del grado dell'espressione node nella lettera name, se
 * node è un polinomio in quella lettera (con le altre lettere come numeri);
 * altrimenti -1: la lettera sta a denominatore, in un esponente o dentro
 * una funzione. */
static int node_letter_degree(const Node *node, int name) {
    long long exponent;
    if (!node_has_variable(node, name)) return 0;
    int a = node->a ? node_letter_degree(node->a, name) : 0, b = node->b ? node_letter_degree(node->b, name) : 0;
    if (a < 0 || b < 0) return -1;
    switch (node->kind) {
    case N_VAR: return 1;
    case N_NEG: return a;
    case N_ADD: case N_SUB: return a > b ? a : b;
    case N_MUL: return a + b;
    case N_DIV: return node_has_variable(node->b, name) ? -1 : a;
    case N_POW: return matrix_exponent_value(node->b, &exponent) && exponent >= 0 && exponent < MAX_UPOLY ? a * (int)exponent : -1;
    default: return -1;
    }
}

/* Come node_letter_degree(), per un'espressione tra matrici: un limite del
 * grado dei suoi elementi nella lettera name, o -1. Un determinante, un
 * rango o un'inversa di qualcosa che contiene la lettera non sono polinomi
 * che qui si sappiano limitare. */
static int matrix_letter_degree(const MatrixNode *node, int name) {
    int a = node->a ? matrix_letter_degree(node->a, name) : 0, b = node->b ? matrix_letter_degree(node->b, name) : 0, top = 0;
    if (a < 0 || b < 0) return -1;
    switch (node->kind) {
    case M_SCALAR:
        return node_letter_degree(node->scalar, name);
    case M_TABLE:
        for (int i = 0; i < node->rows * node->cols; i++) {
            int degree = node_letter_degree(node->entry[i], name);
            if (degree < 0) return -1;
            if (degree > top) top = degree;
        }
        return top;
    case M_IDENTITY: return 0;
    case M_NEG: case M_TRANSPOSE: case M_TRACE: return a;
    case M_ADD: case M_SUB: return a > b ? a : b;
    case M_MUL: return a + b;
    case M_POWER: return !a ? 0 : node->power >= 0 && node->power < MAX_UPOLY ? a * (int)node->power : -1;
    default: return a ? -1 : 0;
    }
}

/* Ritorna il valore numero sample tra quelli che si danno al parametro per
 * calcolare: 0, 1, -1, 2, -2, ... */
static Frac parameter_sample(int sample) { return frac_int(sample % 2 ? (sample + 1) / 2 : -(sample / 2)); }

/* Mette in *a e *b la matrice dei coefficienti e la colonna dei termini noti
 * del sistema di st come matrici di polinomi nel parametro, la lettera
 * letter_name[0]. I coefficienti sono polinomi di grado al più quello che la
 * scrittura consente (node_letter_degree()): si trovano dai loro valori in
 * tanti punti quanti quel grado più uno, e in ogni punto il conto è quello
 * di 33a, con la sua rilettura ricontrollata.
 *
 * Un limite del grado sbagliato darebbe altri polinomi senza che nulla qui
 * se ne accorga, e il certificato parlerebbe di un altro sistema: per questo
 * i polinomi trovati si ricontrollano in un punto in più, che non è servito
 * a trovarli. */
static void linear_polynomials(const LinearStatement *st, const MatrixStatement *names, PMatrix *a, PMatrix *b) {
    Frac x[MAX_UPOLY], *values = NULL;
    int degree = 0, m = 0, n = st->dimension, row, col;
    *a = *b = NO_PMATRIX;

    /* Il limite del grado: il più alto tra quelli dei membri. */
    for (int i = 0; i < (st->vector ? 1 : st->equations) && degree >= 0; i++) {
        int left = st->vector ? matrix_letter_degree(st->matrix_left, letter_name[0]) : node_letter_degree(st->left[i], letter_name[0]);
        int right = st->vector ? matrix_letter_degree(st->matrix_right, letter_name[0]) : node_letter_degree(st->right[i], letter_name[0]);
        degree = left < 0 || right < 0 ? -1 : left > degree ? left : degree;
        if (right > degree && degree >= 0) degree = right;
    }
    if (degree < 0 || degree + 1 > MAX_UPOLY) { fail(PARAMETER_SHAPE); return; }

    /* I valori nei punti: values[(elemento) * (degree + 1) + punto], con gli
     * elementi di A per righe e poi quelli di b. */
    for (int s = 0; s <= degree && !failure; s++) {
        Matrix value_a, value_b;
        x[s] = letter_value[0] = parameter_sample(s);
        linear_solution(st, names, &value_a, &value_b);
        if (failure) return;
        if (!values) {
            m = value_a.rows;
            if (m > MAX_PARAMETER_SIDE) { fail(PARAMETER_SIZE); return; }
            values = arena_alloc((size_t)m * (size_t)(n + 1) * (size_t)(degree + 1) * sizeof *values);
            if (!values) return;
        }
        for (int i = 0; i < m * n; i++) values[i * (degree + 1) + s] = value_a.at[i];
        for (int i = 0; i < m; i++) values[(m * n + i) * (degree + 1) + s] = value_b.at[i];
    }
    *a = pm_new(m, n);
    *b = pm_new(m, 1);
    for (int i = 0; i < m * n && !failure; i++) a->at[i] = up_interpolate(x, &values[i * (degree + 1)], degree + 1);
    for (int i = 0; i < m && !failure; i++) b->at[i] = up_interpolate(x, &values[(m * n + i) * (degree + 1)], degree + 1);

    /* Il punto in più. */
    Matrix value_a, value_b;
    letter_value[0] = parameter_sample(degree + 1);
    linear_solution(st, names, &value_a, &value_b);
    if (!failure && (!matrix_same(pm_value(*a, letter_value[0]), value_a, &row, &col) || !matrix_same(pm_value(*b, letter_value[0]), value_b, &row, &col)))
        linear_reading_failed();
}

/* Mette in col[] le colonne dei perni della forma ridotta della matrice di
 * numeri a, in ordine, e ne ritorna il numero, che è il rango: quelle
 * colonne di a sono indipendenti e generano le altre (32b). a non cambia. */
static int matrix_pivot_columns(Matrix a, int *col) {
    Matrix copy = matrix_new(a.rows, a.cols);
    if (failure) return 0;
    memcpy(copy.at, a.at, (size_t)a.rows * (size_t)a.cols * sizeof(Frac));
    int rank = matrix_reduce(copy, a.cols);
    for (int i = 0; i < rank && !failure; i++) {
        col[i] = 0;
        while (matrix_at(copy, i, col[i])->num == 0) col[i]++;
    }
    return failure ? 0 : rank;
}

/* Il rango generico di una matrice di polinomi (vedi la testa del
 * paragrafo): le righe e le colonne del minore scelto, il suo determinante
 * e la sua aggiunta. */
typedef struct {
    int rank;                                           /* r */
    int row[MAX_PARAMETER_SIDE], col[MAX_PARAMETER_SIDE];  /* le righe R e le colonne C, in ordine */
    UPoly minor;                                        /* d; il numero 1 se r è zero */
    PMatrix adjugate;                                   /* adj(M), r x r; senza elementi se r è zero */
} GenericRank;

/* Ritorna il rango generico della matrice di polinomi a, con (G2)
 * controllata. */
static GenericRank generic_rank(PMatrix a) {
    GenericRank g;
    g.rank = 0;
    g.minor = up_number(frac_int(1));
    g.adjugate = NO_PMATRIX;
    if (failure) return g;
    if (a.rows > MAX_PARAMETER_SIDE || a.cols > MAX_PARAMETER_SIDE) { fail(PARAMETER_SIZE); return g; }

    /* La matrice nulla ha rango zero per ogni valore. */
    if (pm_first(a) < 0) return g;
    for (int sample = 0; sample < GENERIC_SAMPLES && !failure; sample++) {
        size_t mark = arena_used;
        Matrix value = pm_value(a, parameter_sample(sample));
        int r = matrix_pivot_columns(value, g.col);
        if (!failure && matrix_pivot_columns(matrix_transpose(value), g.row) != r) matrix_witness_failed();
        if (!failure && r > MAX_GENERIC) fail(PARAMETER_SIZE);
        if (!failure && r) {
            PMatrix minor = pm_pick(a, g.row, r, g.col, r);
            g.minor = pm_det(minor);
            g.adjugate = pm_adjugate(minor);
            PMatrix through = pm_mul(pm_mul(pm_pick(a, NULL, 0, g.col, r), g.adjugate), pm_pick(a, g.row, r, NULL, 0));
            if (pm_same(pm_scale(a, g.minor), through)) {
                g.rank = r;
                return g;
            }
        }

        /* Un valore speciale: la memoria di questo tentativo si restituisce. */
        arena_used = mark;
    }
    if (!failure) fail("non trovo un valore del parametro in cui la matrice ha il suo rango generico");
    return g;
}

/* Le soluzioni generiche di un sistema A x = b con un parametro (vedi la
 * testa del paragrafo). Le matrici che non servono non hanno elementi. */
typedef struct {
    GenericRank g;
    int solvable;                       /* 1 se genericamente ci sono soluzioni */
    UPoly where;                        /* il polinomio fuori dalle cui radici vale: d, oppure il residuo y b */
    PMatrix combination;                /* senza soluzioni: y, 1 x m */
    PMatrix point;                      /* con soluzioni: N, n x 1; la soluzione è N / d */
    int free;                           /* con soluzioni: le incognite libere, f */
    int free_col[MAX_PARAMETER_SIDE];   /* quali sono, in ordine */
    PMatrix kernel;                     /* con f > 0: n x f, i vettori del nucleo moltiplicati per d */
    PMatrix left;                       /* con soluzioni: n x m; G = left / d */
    PMatrix pick;                       /* con f > 0: f x n, sceglie le incognite libere; T = pick / d */
} GenericSolution;

/* Risolve il sistema a x = b, con a e b matrici di polinomi, nel caso
 * generico, con i testimoni ricontrollati. */
static GenericSolution generic_solve(PMatrix a, PMatrix b) {
    GenericSolution s;
    UPoly one = up_number(frac_int(1)), zero = up_number(frac_int(0));
    memset(&s, 0, sizeof s);
    s.combination = s.point = s.kernel = s.left = s.pick = NO_PMATRIX;
    s.g = generic_rank(a);
    s.where = s.g.minor;
    if (failure) return s;
    int m = a.rows, n = a.cols, r = s.g.rank;
    PMatrix adj_rows = r ? pm_mul(s.g.adjugate, pm_pick(a, s.g.row, r, NULL, 0)) : NO_PMATRIX;
    PMatrix adj_b = r ? pm_mul(s.g.adjugate, pm_pick(b, s.g.row, r, NULL, 0)) : NO_PMATRIX;

    /* I residui: una riga con il residuo non nullo dà la combinazione y. */
    for (int i = 0; i < m && !failure; i++) {
        PMatrix across = r ? pm_pick(a, &i, 1, s.g.col, r) : NO_PMATRIX;
        UPoly residual = up_mul(s.g.minor, *pm_at(b, i, 0));
        if (r) residual = up_add(residual, pm_mul(across, adj_b).at[0], -1);
        if (failure || residual.degree < 0) continue;
        s.where = residual;
        s.combination = pm_new(1, m);
        PMatrix weights = r ? pm_mul(across, s.g.adjugate) : NO_PMATRIX;
        if (failure) return s;
        *pm_at(s.combination, 0, i) = s.g.minor;
        for (int t = 0; t < r; t++) *pm_at(s.combination, 0, s.g.row[t]) = up_add(zero, weights.at[t], -1);
        if (pm_first(pm_mul(s.combination, a)) >= 0) matrix_witness_failed();
        return s;
    }
    if (failure) return s;

    /* Le soluzioni: N e G dalle colonne C, i vettori dalle colonne libere. */
    s.point = pm_new(n, 1);
    s.left = pm_new(n, m);
    for (int j = 0; j < n; j++) {
        int pivot = 0;
        for (int t = 0; t < r; t++) pivot |= s.g.col[t] == j;
        if (!pivot) s.free_col[s.free++] = j;
    }
    if (s.free) {
        s.kernel = pm_new(n, s.free);
        s.pick = pm_new(s.free, n);
    }
    if (failure) return s;
    for (int t = 0; t < r; t++) {
        *pm_at(s.point, s.g.col[t], 0) = adj_b.at[t];
        for (int u = 0; u < r; u++) *pm_at(s.left, s.g.col[t], s.g.row[u]) = *pm_at(s.g.adjugate, t, u);
    }
    for (int q = 0; q < s.free; q++) {
        *pm_at(s.kernel, s.free_col[q], q) = s.g.minor;
        *pm_at(s.pick, q, s.free_col[q]) = one;
        for (int t = 0; t < r; t++) *pm_at(s.kernel, s.g.col[t], q) = up_add(zero, *pm_at(adj_rows, t, s.free_col[q]), -1);
    }

    /* (S1), (S2), (S3) tra matrici di polinomi. */
    PMatrix spans = pm_mul(s.left, a);
    if (s.free) spans = pm_add(spans, pm_mul(s.kernel, s.pick), 1);
    if (!pm_same(pm_mul(a, s.point), pm_scale(b, s.g.minor)) || (s.free && pm_first(pm_mul(a, s.kernel)) >= 0) ||
        !pm_same(spans, pm_diagonal(n, s.g.minor))) matrix_witness_failed();
    s.solvable = !failure;
    return s;
}

/* Riduce la frazione di polinomi num / den, con den non nullo, alla
 * scrittura dei libri: senza fattori comuni (il massimo comun divisore,
 * con Euclide), con i coefficienti interi senza divisori comuni e il
 * coefficiente direttivo del denominatore positivo. Una frazione che vale
 * zero diventa 0 / 1. */
static void up_reduce(UPoly *num, UPoly *den) {
    UPoly quotient, common = up_gcd(*num, *den);
    __int128 scale = 1, content = 0;
    if (failure) return;
    if (num->degree < 0) { *den = up_number(frac_int(1)); return; }
    up_divide(*num, common, &quotient);
    *num = quotient;
    up_divide(*den, common, &quotient);
    *den = quotient;

    /* I denominatori dei coefficienti, poi i divisori comuni dei numeratori.
     * Il limite si guarda a ogni passo: due numeri sotto COEF_LIMIT hanno un
     * prodotto che sta in 128 bit, tre no. */
    for (int side = 0; side < 2; side++)
        for (int i = 0; i <= (side ? den : num)->degree; i++) {
            scale = scale / gcd128(scale, (side ? den : num)->at[i].den) * (side ? den : num)->at[i].den;
            if (scale >= COEF_LIMIT) { fail("numeri troppo grandi per il calcolo esatto"); return; }
        }
    for (int side = 0; side < 2; side++)
        for (int i = 0; i <= (side ? den : num)->degree; i++) {
            Frac *c = &(side ? den : num)->at[i];
            *c = frac_mul(*c, frac_make(scale, 1));
            content = gcd128(content, c->num);
        }
    if (failure || content == 0) return;
    if (den->at[den->degree].num < 0) content = -content;
    for (int side = 0; side < 2; side++)
        for (int i = 0; i <= (side ? den : num)->degree; i++) (side ? den : num)->at[i] = frac_div((side ? den : num)->at[i], frac_make(content, 1));
}

/* Aggiunge a text, di size byte, la frazione num / den nella lettera
 * letter, ridotta: un polinomio se il denominatore è un numero, altrimenti
 * \frac{...}{...}. */
static void up_fraction_latex(UPoly num, UPoly den, int letter, char *text, size_t size) {
    up_reduce(&num, &den);
    if (failure) return;
    if (den.degree == 0) {
        for (int i = 0; i <= num.degree; i++) num.at[i] = frac_div(num.at[i], den.at[0]);
        up_latex(&num, letter, text, size);
        return;
    }
    text_add(text, size, "\\frac{");
    up_latex(&num, letter, text, size);
    text_add(text, size, "}{");
    up_latex(&den, letter, text, size);
    text_add(text, size, "}");
}

/* Mette in letter[] le prime count lettere di un elenco che non sono già
 * incognite di st né lettere a cui l'enunciato ha dato un valore: sono i
 * parametri di un insieme di soluzioni scritto. Ritorna 0, annotando
 * l'errore, se non bastano. */
static int linear_letters(const LinearStatement *st, int count, char *letter) {
    static const char names[] = "tsuvwpqrabcdfghjklmnxyz";
    int found = 0;
    for (const char *p = names; *p && found < count; p++) {
        int taken = 0;
        for (int i = 0; i < st->unknowns; i++) taken |= st->unknown[i].name == *p;
        for (int i = 0; i < letter_count; i++) taken |= letter_name[i] == *p;
        if (!taken) letter[found++] = *p;
    }
    if (found < count) fail("non ci sono abbastanza lettere per i parametri delle soluzioni");
    return found == count;
}

/* Scrive in text, di size byte, le soluzioni generiche s del sistema di st
 * come nei libri, con il parametro letter_name[0] nelle componenti: la
 * soluzione particolare N / d con ogni frazione ridotta, e i vettori del
 * nucleo divisi per il massimo comun divisore delle loro componenti, che
 * fuori dai valori speciali non si annulla. È scritto in modo che 31s lo
 * rilegga. */
static void generic_answer(const LinearStatement *st, const GenericSolution *s, char *text, size_t size) {
    char letter[MAX_UNKNOWNS];
    int k = letter_name[0], n = st->dimension;
    if (!s->solvable) { text_add(text, size, "\\emptyset"); return; }
    if (!linear_letters(st, s->free, letter)) return;
    text_add(text, size, "\\{");
    if (!s->free || pm_first(s->point) >= 0) {
        text_add(text, size, "(");
        for (int i = 0; i < n && !failure; i++) {
            if (i) text_add(text, size, ", ");
            up_fraction_latex(*pm_at(s->point, i, 0), s->g.minor, k, text, size);
        }
        text_add(text, size, ")");
    }
    for (int q = 0; q < s->free && !failure; q++) {
        /* Il vettore, diviso per ciò che le sue componenti hanno in comune:
         * ogni componente come frazione con quel divisore a denominatore. */
        UPoly common = up_number(frac_int(0));
        for (int i = 0; i < n; i++) common = up_gcd(common, *pm_at(s->kernel, i, q));
        text_add(text, size, "%s%c (", q || pm_first(s->point) >= 0 ? " + " : "", letter[q]);
        for (int i = 0; i < n && !failure; i++) {
            if (i) text_add(text, size, ", ");
            up_fraction_latex(*pm_at(s->kernel, i, q), common, k, text, size);
        }
        text_add(text, size, ")");
    }
    for (int q = 0; q < s->free; q++) text_add(text, size, "%s%c", q ? ", " : " \\mid ", letter[q]);
    text_add(text, size, s->free ? " \\in \\mathbb{R}\\}" : "\\}");
}

/* Ritorna il polinomio nella lettera name che l'albero node scrive; annota
 * un errore se non è un polinomio in quella lettera. Ciò che non la contiene
 * è un numero di matrix_number(). */
static UPoly up_from_node(const Node *node, int name) {
    UPoly zero = up_number(frac_int(0)), p;
    long long exponent;
    if (failure) return zero;
    if (!node_has_variable(node, name)) return up_number(matrix_number(node));
    switch (node->kind) {
    case N_VAR:
        p.degree = 1;
        p.at[0] = frac_int(0);
        p.at[1] = frac_int(1);
        return p;
    case N_NEG:
        return up_add(zero, up_from_node(node->a, name), -1);
    case N_ADD: case N_SUB:
        p = up_from_node(node->a, name);
        return up_add(p, up_from_node(node->b, name), node->kind == N_ADD ? 1 : -1);
    case N_MUL:
        p = up_from_node(node->a, name);
        return up_mul(p, up_from_node(node->b, name));
    case N_DIV:
        if (node_has_variable(node->b, name)) break;
        return up_mul(up_from_node(node->a, name), up_number(frac_div(frac_int(1), matrix_number(node->b))));
    case N_POW: {
        if (!matrix_exponent_value(node->b, &exponent) || exponent < 0 || exponent >= MAX_UPOLY) break;
        UPoly base = up_from_node(node->a, name);
        p = up_number(frac_int(1));
        for (long long i = 0; i < exponent && !failure; i++) p = up_mul(p, base);
        return p;
    }
    default:
        break;
    }
    fail(PARAMETER_SHAPE);
    return zero;
}

/* Guarda l'albero node di un insieme scritto con il parametro name:
 * moltiplica in *mult il polinomio di ogni divisore che contiene il
 * parametro, e ritorna un limite del grado di numeratore e denominatore di
 * node come frazione di polinomi (la somma dei gradi di tutto ciò che è
 * scritto: una somma di frazioni ha per numeratore i prodotti in croce, e
 * il loro grado non supera la somma dei gradi dei pezzi). Annota un errore
 * se il parametro sta dentro una radice, una funzione o un esponente. */
static int stated_divisors(const Node *node, int name, UPoly *mult) {
    long long exponent;
    if (failure || !node || !node_has_variable(node, name)) return 0;
    switch (node->kind) {
    case N_VAR:
        return 1;
    case N_NEG: case N_ADD: case N_SUB: case N_MUL:
        return stated_divisors(node->a, name, mult) + stated_divisors(node->b, name, mult);
    case N_DIV:
        if (node_has_variable(node->b, name)) *mult = up_mul(*mult, up_from_node(node->b, name));
        return stated_divisors(node->a, name, mult) + node_letter_degree(node->b, name);
    case N_POW:
        if (!matrix_exponent_value(node->b, &exponent) || exponent <= -MAX_UPOLY || exponent >= MAX_UPOLY) break;
        if (exponent >= 0) {
            /* I divisori dentro la base contano una volta per fattore. */
            int degree = 0;
            for (long long i = 0; i < exponent && !failure; i++) degree += stated_divisors(node->a, name, mult);
            return degree;
        }
        for (long long i = 0; i < -exponent && !failure; i++) *mult = up_mul(*mult, up_from_node(node->a, name));
        return (int)-exponent * node_letter_degree(node->a, name);
    default:
        break;
    }
    fail(PARAMETER_SHAPE);
    return 0;
}

/* Mette in *mult, *point e *directions l'insieme scritto di st, o il vettore
 * di cui st parla, con il parametro letter_name[0] nelle componenti (vedi la
 * testa del paragrafo): il punto è point / mult, i vettori le colonne di
 * directions / mult (matrici di polinomi; directions senza elementi se non
 * ci sono parametri). Annota un errore se un divisore è il polinomio nullo. */
static void stated_polynomials(const LinearStatement *st, UPoly *mult, PMatrix *point, PMatrix *directions) {
    const VectorSum *sum = &st->stated;
    Frac x[MAX_UPOLY], *values;
    int n = sum->size, f = st->parameters, bound = 0, found = 0;
    *mult = up_number(frac_int(1));
    *point = *directions = NO_PMATRIX;

    /* I divisori, e il limite del grado: quello di mult più quello di tutto
     * ciò che è scritto. */
    for (int t = 0; t < sum->terms && !failure; t++) {
        bound += stated_divisors(sum->term[t].factor, letter_name[0], mult);
        for (int c = 0; c < n; c++) bound += stated_divisors(sum->term[t].entry[c], letter_name[0], mult);
    }

    /* Un divisore che è zero per ogni valore del parametro, come k - k:
     * l'insieme scritto non è definito in nessun valore, e l'enunciato non
     * ha senso. Va detto qui: i due cicli qui sotto cercano i valori in cui
     * mult non si annulla, e con mult nullo non finirebbero mai (è successo,
     * con \frac{1}{k - k} in una componente). */
    if (!failure && mult->degree < 0) fail("un divisore dell'insieme scritto è zero per ogni valore del parametro: l'insieme non è definito");
    bound += mult->degree;
    if (!failure && bound + 1 > MAX_UPOLY) fail("con un parametro i polinomi che servono hanno un grado troppo alto");
    values = failure ? NULL : arena_alloc((size_t)n * (size_t)(f + 1) * (size_t)(bound + 1) * sizeof *values);
    if (!values) return;

    /* I valori, nei punti in cui nessun divisore si annulla: ogni
     * componente, del punto e dei vettori, moltiplicata per mult. */
    for (int sample = 0; found <= bound && !failure; sample++) {
        Matrix p, u;
        Frac scale = up_at(mult, parameter_sample(sample));
        if (scale.num == 0) continue;
        x[found] = letter_value[0] = parameter_sample(sample);
        linear_stated(st, &p, &u);
        for (int i = 0; i < n && !failure; i++) {
            values[(i * (f + 1) + f) * (bound + 1) + found] = frac_mul(scale, *matrix_at(p, i, 0));
            for (int j = 0; j < f; j++) values[(i * (f + 1) + j) * (bound + 1) + found] = frac_mul(scale, *matrix_at(u, i, j));
        }
        found++;
    }
    *point = pm_new(n, 1);
    if (f) *directions = pm_new(n, f);
    for (int i = 0; i < n && !failure; i++) {
        *pm_at(*point, i, 0) = up_interpolate(x, &values[(i * (f + 1) + f) * (bound + 1)], bound + 1);
        for (int j = 0; j < f && !failure; j++) *pm_at(*directions, i, j) = up_interpolate(x, &values[(i * (f + 1) + j) * (bound + 1)], bound + 1);
    }

    /* Un punto in più, che non è servito a trovare i polinomi: lì l'insieme
     * scritto, calcolato sui numeri, deve essere quello che i polinomi
     * dicono (vedi linear_polynomials()). */
    for (int sample = 0, checked = 0; !checked && !failure; sample++) {
        Matrix p, u;
        int row, col, used = 0;
        Frac at = parameter_sample(sample), scale = up_at(mult, at);
        for (int i = 0; i <= bound; i++) used |= frac_cmp(x[i], at) == 0;
        if (used || scale.num == 0) continue;
        letter_value[0] = at;
        linear_stated(st, &p, &u);
        if (!failure && (!matrix_same(pm_value(*point, at), matrix_scale(p, scale), &row, &col) ||
                         (f && !matrix_same(pm_value(*directions, at), matrix_scale(u, scale), &row, &col)))) linear_reading_failed();
        checked = 1;
    }
}

/* 33h. LA DISCUSSIONE: UN FATTO DIVENTA UNA CONDIZIONE SUL PARAMETRO
 *
 * A che cosa serve. Con un parametro k, "il rango è 2" e "il sistema è
 * impossibile" non sono veri o falsi: lo sono per certi valori di k. Un
 * enunciato dei libri dice per quali:
 *
 *     \forall k \in \mathbb{R}\ (\operatorname{rank} A = 2 \iff k = 5)
 *     \{k \in \mathbb{R} \mid \{(x, y, z) \in \mathbb{R}^{3} \mid ...\} = \emptyset\}
 *
 * e una richiesta, "discutere il sistema al variare di k", vuole l'elenco
 * dei casi. Il programma sa già decidere gli enunciati in una lettera reale
 * (la tabella dei segni, 18p), purché siano fatti di confronti tra
 * espressioni in k. Qui ogni fatto di algebra lineare (un rango confrontato
 * con un numero, un insieme di soluzioni confrontato con un insieme scritto)
 * diventa la condizione su k che dice dove vale, e l'enunciato che resta
 * passa a quelle regole, come 32g fa con i determinanti.
 *
 * Un fatto si discute così:
 *
 *   h1. il caso generico (33g) dà la verità del fatto per ogni k che non
 *       annulla un polinomio D, con il suo certificato, che lo dichiara
 *       nella voce where;
 *   h2. i valori speciali sono le radici reali di D. Si cercano quelle
 *       razionali (up_rational_roots()), e in ognuna il fatto si decide sui
 *       numeri, con i certificati a testimoni di 33d e di 32f;
 *   h3. la condizione è "k è uno dei valori speciali in cui il fatto vale",
 *       oppure, se il fatto vale nel caso generico, anche "k non è nessuno
 *       dei valori speciali";
 *   h4. che D non abbia altre radici reali, cioè che i valori speciali siano
 *       tutti, è a sua volta un enunciato in una lettera: "D = 0 se e solo
 *       se k = ... \lor k = ...", e lo dimostra la tabella dei segni, con il
 *       suo certificato (le radici contate con il teorema di Sturm). Se D ha
 *       una radice irrazionale quell'enunciato è falso, e la discussione si
 *       ferma: lì servirebbe il conto con i radicali.
 *
 * Un insieme scritto che in un valore speciale non è definito (il parametro
 * annulla un suo denominatore) lì non è uguale a nulla: il fatto non vale,
 * come un confronto con un membro non definito nella tabella dei segni.
 *
 * UNA RICHIESTA con il parametro, \forall k \in \mathbb{R}\ seguito da un
 * insieme di soluzioni o da un rango, ha per risposta i casi: per ogni
 * valore speciale le soluzioni di lì, e per gli altri la formula generica.
 * Ciò che si consegna si rilegge: i casi scritti diventano l'enunciato
 * "(k = 5 e le soluzioni sono queste) oppure ... oppure (k non è nessuno di
 * quelli e le soluzioni sono queste)", che ripassa da capo per la
 * discussione, fatto per fatto, e deve risultare dimostrato.
 *
 * CHE COSA È CERTIFICATO. Ogni fatto porta i suoi certificati: quello
 * generico, uno per valore speciale, e quello della tabella dei segni per
 * le radici di D. L'enunciato che resta ha il suo, quando il suo metodo lo
 * scrive. Che l'enunciato che resta sia quello di partenza con ogni fatto
 * sostituito dalla sua condizione è lettura.
 *
 * Che cosa resta fuori: il caso generico di un insieme scritto più piccolo
 * delle soluzioni, o con vettori di troppo (il fatto lì è falso o vero, ma
 * non c'è ancora il testimone con il parametro che lo mostri); l'inversa con
 * il parametro; un vettore e la sua appartenenza con il parametro; un rango
 * scritto a destra del confronto. Il verdetto lo dice.
 */

#define MAX_FACTS 16       /* fatti discussi in un enunciato */
#define REQUEST_TEXT 2048  /* lunghezza delle soluzioni di un caso */

/* Che cosa la discussione dice di un fatto (vedi qui sopra): i valori
 * speciali in ordine crescente, con la verità del fatto in ognuno, e la
 * verità nel caso generico. */
typedef struct {
    int values;
    Frac value[MAX_SPECIAL];
    int truth[MAX_SPECIAL];
    int generic;  /* 1 se vale, 0 se non vale, -1 se non si è saputo stabilire */
} Discussion;

/* Ciò che le discussioni dell'enunciato in corso lasciano: i certificati
 * accettati, uno dopo l'altro; e per ogni fatto l'enunciato h4 sulle radici
 * del suo polinomio, da far dimostrare alla fine (vuoto se il polinomio è
 * un numero). discussion_unproved dice se una discussione si è fermata
 * perché il verificatore non ha accettato un certificato. */
static _Thread_local char discussion_certificates[CERTIFICATE_BYTES], discussion_roots[MAX_FACTS][1024];
static _Thread_local int discussion_facts, discussion_unproved;

/* Aggiunge ai certificati della discussione quello appena accettato, che
 * sta in certificate_text. */
static void discussion_keep(void) {
    text_add(discussion_certificates, sizeof discussion_certificates, "%s%s", discussion_certificates[0] ? "\n" : "", certificate_text);
}

/* Fa controllare al verificatore il certificato in certificate_text. Se non
 * lo accetta ferma il conto con il motivo; se lo accetta lo conserva. */
static void discussion_check(void) {
    static _Thread_local char problem[512];
    const char *why = "il certificato non si può scrivere", *text = certificate_text;
    if (failure) return;
    CkAnswer checked = certificate_broken ? CK_UNSUPPORTED : ck_check(&text, &why, checker_steps());
    if (checked == CK_ACCEPTED) { discussion_keep(); return; }
    if (checked == CK_REJECTED) unjustified_steps++;
    discussion_unproved = 1;
    snprintf(problem, sizeof problem, checked == CK_REJECTED ? "il verificatore indipendente ha respinto il certificato di un caso della discussione: %s"
                                                             : "il verificatore non sa controllare il certificato di un caso della discussione: %s", why);
    fail(problem);
}

/* Comincia in certificate_text il certificato di un caso generico, che vale
 * dove il polinomio where non si annulla, fino alla parola statement. */
static void generic_header(const UPoly *where) {
    certificate_length = 0;
    certificate_broken = 0;
    cert_add("certificate matrices\nletters %c\nwhere ", letter_name[0]);
    cert_upoly(where, letter_name[0]);
    cert_add("\nstatement ");
}

/* h2, h4. Mette in d i valori speciali, le radici razionali dei polinomi
 * factor[0], ..., factor[factors - 1] (il polinomio D è il loro prodotto), e
 * prepara l'enunciato che dice che D non ha altre radici reali. Lo scrive
 * con i fattori separati: sono di grado più basso del prodotto. */
static void discussion_special(Discussion *d, const UPoly *factor, int factors) {
    char *statement = discussion_roots[discussion_facts], number[64];
    int k = letter_name[0], constant = 1, written = 0;
    d->values = 0;
    if (failure) return;
    if (discussion_facts == MAX_FACTS) { fail("troppi fatti da discutere in un enunciato con un parametro"); return; }
    for (int f = 0; f < factors && !failure; f++) {
        Frac root[MAX_SPECIAL];
        int roots = up_rational_roots(factor[f], root, MAX_SPECIAL);
        constant = constant && factor[f].degree == 0;
        for (int i = 0; i < roots && !failure; i++) {
            int place = 0, known = 0;
            while (place < d->values && frac_cmp(d->value[place], root[i]) < 0) place++;
            known = place < d->values && frac_cmp(d->value[place], root[i]) == 0;
            if (known) continue;
            if (d->values == MAX_SPECIAL) { fail("troppi valori speciali del parametro"); return; }
            for (int j = d->values++; j > place; j--) d->value[j] = d->value[j - 1];
            d->value[place] = root[i];
        }
    }

    /* h4. "D = 0 se e solo se k è uno di questi", o "D non è mai zero". */
    statement[0] = 0;
    discussion_facts++;
    if (failure || constant) return;
    text_add(statement, sizeof discussion_roots[0], "\\forall %c \\in \\mathbb{R}\\ \\left( ", k);
    for (int f = 0; f < factors; f++) {
        if (factor[f].degree == 0) continue;
        text_add(statement, sizeof discussion_roots[0], "%s\\left( ", written++ ? " \\cdot " : "");
        up_latex(&factor[f], k, statement, sizeof discussion_roots[0]);
        text_add(statement, sizeof discussion_roots[0], " \\right)");
    }
    text_add(statement, sizeof discussion_roots[0], d->values ? " = 0 \\iff \\left( " : " \\neq 0");
    for (int i = 0; i < d->values; i++) {
        number[0] = 0;
        frac_latex(d->value[i], number, sizeof number);
        text_add(statement, sizeof discussion_roots[0], "%s%c = %s", i ? " \\lor " : "", k, number);
    }
    text_add(statement, sizeof discussion_roots[0], d->values ? " \\right) \\right)" : " \\right)");
}

/* Aggiunge alla dimostrazione in corso l'inizio di un caso: "At k = 5: ". */
static void discussion_case(Frac value) {
    char number[64] = "";
    frac_latex(value, number, sizeof number);
    proof_add(" At $%c = %s$: ", letter_name[0], number);
}

/* Ritorna 1 se nell'espressione tra matrici node compare la lettera name. */
static int matrix_has_letter(const MatrixNode *node, int name) {
    if (!node) return 0;
    if (node->kind == M_SCALAR) return node_has_variable(node->scalar, name);
    for (int i = 0; node->kind == M_TABLE && i < node->rows * node->cols; i++)
        if (node_has_variable(node->entry[i], name)) return 1;
    return matrix_has_letter(node->a, name) || matrix_has_letter(node->b, name);
}

/* Ritorna 1 se nel fatto st compare la lettera name: nel sistema, oppure
 * nell'insieme scritto. */
static int linear_has_letter(const LinearStatement *st, int name) {
    if (st->vector && (matrix_has_letter(st->matrix_left, name) || matrix_has_letter(st->matrix_right, name))) return 1;
    for (int i = 0; i < st->equations; i++)
        if (node_has_variable(st->left[i], name) || node_has_variable(st->right[i], name)) return 1;
    for (int t = 0; t < st->stated.terms; t++) {
        if (node_has_variable(st->stated.term[t].factor, name)) return 1;
        for (int c = 0; c < st->stated.size; c++)
            if (node_has_variable(st->stated.term[t].entry[c], name)) return 1;
    }
    return 0;
}

/* Discute il fatto st, un insieme di soluzioni con il parametro
 * letter_name[0] confrontato con un insieme scritto (h1, h2), e ne
 * conserva i certificati. */
static Discussion discuss_system(const LinearStatement *st, const MatrixStatement *names) {
    Discussion d = {0, {{0, 1}}, {0}, -1};
    UPoly one = up_number(frac_int(1)), mult = one, factor[3], where = one;
    PMatrix a, b, point = NO_PMATRIX, directions = NO_PMATRIX, top = NO_PMATRIX;
    int k = letter_name[0], equal = -1, factors = 0, f = st->parameters;

    /* Un fatto in cui il parametro non compare vale, o non vale, per ogni
     * suo valore: lo decide una volta il conto sui numeri, con il suo
     * certificato, e non ha valori speciali. */
    if (!linear_has_letter(st, k)) {
        LinearEvidence e;
        Outcome outcome;
        const char *problem = linear_settle(st, names, &d.generic, &e, &outcome);
        if (problem) {
            discussion_unproved |= outcome == NOT_PROVED;
            fail(problem);
            d.generic = -1;
            return d;
        }
        discussion_keep();
        discussion_special(&d, &one, 1);
        return d;
    }
    linear_polynomials(st, names, &a, &b);
    GenericSolution s = generic_solve(a, b);
    if (!failure && !st->empty && st->stated.size != st->dimension) fail("i vettori scritti non hanno tante componenti quante sono le incognite del sistema");
    if (failure) return d;

    /* h1. Il caso generico: gli insiemi sono uguali, diversi, o non si sa. */
    if (st->empty) {
        equal = !s.solvable;
        factor[factors++] = s.where;
    } else {
        stated_polynomials(st, &mult, &point, &directions);
        if (failure) return d;
        PMatrix residual = pm_add(pm_mul(a, point), pm_scale(b, mult), -1), image = f ? pm_mul(a, directions) : NO_PMATRIX;
        int wrong = pm_first(residual), outside = f ? pm_first(image) : -1;
        if (failure) return d;
        factor[factors++] = mult;
        if (wrong >= 0 || outside >= 0) {
            /* Il punto, o un vettore, non risolve: lo dice un polinomio non
             * nullo, e dove quello non si annulla gli insiemi sono diversi. */
            equal = 0;
            factor[factors++] = wrong >= 0 ? residual.at[wrong] : image.at[outside];
        } else if (!s.solvable) {
            matrix_witness_failed();
        } else if (f == s.free) {
            factor[factors++] = s.g.minor;
            equal = 1;
            if (f) {
                /* I vettori scritti sono indipendenti dove il determinante
                 * delle loro componenti libere non si annulla. */
                PMatrix q = pm_pick(directions, s.free_col, f, NULL, 0);
                factor[factors] = pm_det(q);
                if (factor[factors].degree < 0) equal = -1;
                else {
                    top = pm_mul(pm_adjugate(q), s.pick);
                    PMatrix spans = pm_add(pm_scale(pm_mul(s.left, a), factor[factors]), pm_scale(pm_mul(directions, top), s.g.minor), 1);
                    if (!pm_same(spans, pm_diagonal(a.cols, up_mul(s.g.minor, factor[factors])))) matrix_witness_failed();
                    factors++;
                }
            }
        }
    }
    if (failure) return d;
    for (int i = 0; i < factors; i++) where = up_mul(where, factor[i]);
    d.generic = equal < 0 ? -1 : (st->relation == LINEAR_EQ) == equal;

    /* Il certificato del caso generico: l'enunciato com'è, con la verità
     * trovata, dove il prodotto dei polinomi non si annulla. */
    if (equal >= 0) {
        generic_header(&where);
        cert_add("(%s (solutions", st->relation == LINEAR_EQ ? "=" : "neq");
        cert_pmatrix(a, k);
        cert_pmatrix(b, k);
        cert_add(")");
        if (st->empty) cert_add(" (nothing)");
        else {
            cert_add(" (affine");
            cert_pmatrix_over(point, &one, &mult, k);
            if (f) cert_pmatrix_over(directions, &one, &mult, k);
            cert_add(")");
        }
        cert_add(")\nclaim %s\n", d.generic ? "true" : "false");
        if (st->empty && equal) {
            cert_add("witness combination");
            cert_pmatrix(s.combination, k);
            cert_add("\n");
        } else if (st->empty) {
            cert_add("witness solution");
            cert_pmatrix_over(s.point, &one, &s.g.minor, k);
            cert_add("\n");
        } else if (equal) {
            cert_add("witness span");
            cert_pmatrix_over(s.left, &one, &s.g.minor, k);
            if (f) cert_pmatrix_over(top, &mult, &factor[factors - 1], k);
            cert_add("\n");
        }
        cert_add("end\n");
        discussion_check();
        proof_add(" For every value of $%c$ outside the special ones the stated relation %s, by the same products with polynomials in $%c$. ", k,
                  d.generic ? "holds" : "does not hold", k);
    }

    /* h2. I valori speciali, e in ognuno il conto sui numeri. */
    discussion_special(&d, factor, factors);
    for (int i = 0; i < d.values && !failure; i++) {
        LinearEvidence e;
        Outcome outcome;
        letter_value[0] = d.value[i];
        undefined = 0;
        discussion_case(d.value[i]);
        const char *problem = linear_settle(st, names, &d.truth[i], &e, &outcome);
        if (problem && failure && undefined) {
            /* L'insieme scritto qui non è definito: il fatto non vale. */
            failure = NULL;
            d.truth[i] = 0;
            proof_add("the written set is not defined, so the stated relation does not hold. ");
        } else if (problem) {
            discussion_unproved |= outcome == NOT_PROVED;
            fail(problem);
        } else discussion_keep();
    }
    return d;
}

/* Un rango confrontato con un numero: \operatorname{rank} A = 2. rank è il
 * nodo del rango, number quello del numero. */
typedef struct {
    MatrixNode *rank, *number;
    MatrixRelation relation;
} RankFact;

/* Mette in *a la matrice di polinomi nel parametro che l'espressione tra
 * matrici node vale: dai suoi valori in abbastanza punti, come
 * linear_polynomials(). */
static void matrix_polynomials(MatrixNode *node, PMatrix *a) {
    Frac x[MAX_UPOLY], *values = NULL;
    int degree = matrix_letter_degree(node, letter_name[0]), rows = 0, cols = 0;
    *a = NO_PMATRIX;
    if (degree < 0 || degree + 1 > MAX_UPOLY) { fail(PARAMETER_SHAPE); return; }
    for (int s = 0; s <= degree && !failure; s++) {
        x[s] = letter_value[0] = parameter_sample(s);
        MatrixValue value = matrix_eval(node, 0);
        if (!failure && !value.is_matrix) fail("determinante, rango e traccia si calcolano di una matrice, non di un numero");
        if (failure) return;
        if (!values) {
            rows = value.matrix.rows;
            cols = value.matrix.cols;
            if (rows > MAX_PARAMETER_SIDE || cols > MAX_PARAMETER_SIDE) { fail(PARAMETER_SIZE); return; }
            values = arena_alloc((size_t)rows * (size_t)cols * (size_t)(degree + 1) * sizeof *values);
            if (!values) return;
        }
        for (int i = 0; i < rows * cols; i++) values[i * (degree + 1) + s] = value.matrix.at[i];
    }
    *a = pm_new(rows, cols);
    for (int i = 0; i < rows * cols && !failure; i++) a->at[i] = up_interpolate(x, &values[i * (degree + 1)], degree + 1);

    /* Il punto in più (vedi linear_polynomials()). */
    int row, col;
    letter_value[0] = parameter_sample(degree + 1);
    MatrixValue value = matrix_eval(node, 0);
    if (!failure && !matrix_same(pm_value(*a, letter_value[0]), value.matrix, &row, &col)) linear_reading_failed();
}

/* Discute il fatto fact, un rango con il parametro letter_name[0]
 * confrontato con un numero (h1, h2), e ne conserva i certificati. */
static Discussion discuss_rank(const RankFact *fact) {
    Discussion d = {0, {{0, 1}}, {0}, -1};
    UPoly one = up_number(frac_int(1));
    PMatrix a;
    char note[256];
    int k = letter_name[0];
    if (node_has_variable(fact->number->scalar, k)) fail("con un parametro un rango si confronta con un numero scritto, senza il parametro");
    matrix_polynomials(fact->rank->a, &a);
    GenericRank g = generic_rank(a);
    if (failure) return d;
    int r = g.rank, m = a.rows, n = a.cols;

    /* h1. Il caso generico: il rango è r dove d non si annulla, con i
     * testimoni di 33g. Che il fatto valga lo dice poi il confronto tra r e
     * il numero scritto. */
    generic_header(&g.minor);
    cert_add("(= (rank ");
    matrix_cert_node(fact->rank->a);
    cert_add(") %d)\nclaim true\nwitness rank %d", r, r);
    if (r) {
        PMatrix up = pm_new(r, m), choose = pm_new(n, r);
        for (int t = 0; t < r && !failure; t++) {
            *pm_at(choose, g.col[t], t) = one;
            for (int u = 0; u < r; u++) *pm_at(up, t, g.row[u]) = *pm_at(g.adjugate, t, u);
        }
        cert_pmatrix(pm_pick(a, NULL, 0, g.col, r), k);
        cert_pmatrix_over(pm_mul(g.adjugate, pm_pick(a, g.row, r, NULL, 0)), &one, &g.minor, k);
        cert_pmatrix_over(up, &one, &g.minor, k);
        cert_pmatrix(choose, k);
    }
    cert_add("\nend\n");
    discussion_check();
    MatrixValue left = {0, frac_int(r), {0, 0, NULL}}, right = {0, matrix_number(fact->number->scalar), {0, 0, NULL}};
    d.generic = matrix_holds(left, right, fact->relation, note, sizeof note);
    proof_add(" For every value of $%c$ outside the special ones the rank is $%d$: a minor of that order has a determinant that does not vanish there, "
              "and the matrix is a product through $%d$ columns. ", k, r, r);

    /* h2. I valori speciali: lì il rango è quello dei numeri, con il suo
     * testimone, e la lettera scritta come il numero che vale. */
    discussion_special(&d, &g.minor, 1);
    for (int i = 0; i < d.values && !failure; i++) {
        const MatrixStatement stated = {fact->rank, fact->number, fact->relation, 0, {NULL}};
        letter_value[0] = d.value[i];
        left = matrix_eval(fact->rank, 0);
        d.truth[i] = matrix_holds(left, right, fact->relation, note, sizeof note);
        if (failure) break;
        discussion_case(d.value[i]);
        proof_add("the rank is $%lld$. ", left.number.num);
        letter_numbers = 1;
        matrix_certificate(&stated, left, right, d.truth[i]);
        letter_numbers = 0;
        discussion_check();
    }
    return d;
}

/* h3. Aggiunge a text, di size byte, la condizione sul parametro che dice
 * dove vale il fatto discusso in d, tra parentesi: i valori speciali in cui
 * vale e, se vale nel caso generico, "nessuno dei valori speciali". Un
 * fatto che non vale mai è la condizione falsa 0 = 1, uno che vale sempre
 * quella vera 0 = 0. */
static void discussion_condition(const Discussion *d, char *text, size_t size) {
    char number[64];
    int k = letter_name[0], written = 0;
    text_add(text, size, "(");
    for (int i = 0; i < d->values; i++) {
        if (!d->truth[i]) continue;
        number[0] = 0;
        frac_latex(d->value[i], number, sizeof number);
        text_add(text, size, "%s%c = %s", written++ ? " \\lor " : "", k, number);
    }
    if (d->generic == 1 && !d->values) text_add(text, size, "%s0 = 0", written++ ? " \\lor " : "");
    else if (d->generic == 1) {
        text_add(text, size, "%s(", written++ ? " \\lor " : "");
        for (int i = 0; i < d->values; i++) {
            number[0] = 0;
            frac_latex(d->value[i], number, sizeof number);
            text_add(text, size, "%s%c \\neq %s", i ? " \\land " : "", k, number);
        }
        text_add(text, size, ")");
    }
    text_add(text, size, written ? ")" : "0 = 1)");
}

/* Ritorna 1 se il token corrente, \{, comincia un insieme di soluzioni di
 * un sistema (31s). Non sposta nulla. */
static int linear_set_here(void) {
    LinearStatement st;
    ParserState here = parser_save();
    const char *here_consumed = consumed;
    memset(&st, 0, sizeof st);
    linear_unknowns(&st);
    int found = !syntax_error;
    parser_restore(here);
    consumed = here_consumed;
    return found;
}

/* Ritorna la lettera del parametro di formula: la sola lettera che un
 * quantificatore, o un insieme \{k \in \mathbb{R} \mid ...\}, mette in tutto
 * \mathbb{R}. Ritorna 0 se non ce n'è nessuna e -1 se sono più di una. Le
 * incognite di un sistema stanno in \mathbb{R} con un esponente, e i
 * parametri di un insieme scritto seguono \mid: non contano. Usa il lettore
 * di token del parser, e lascia il suo stato da reimpostare. */
static int parameter_of(const char *formula) {
    int letter = 0;
    syntax_error = NULL;
    cursor = formula;
    for (next_token(); token.kind != T_END && letter >= 0; ) {
        int opens = is_command("forall") || is_command("exists") || is_char(ESCAPED + '{');
        next_token();
        if (!opens || token.kind != T_LETTER || !islower(token.ch)) continue;
        int name = token.ch;
        next_token();
        if (!is_command("in")) continue;

        /* \mathbb{R}, e nessun esponente. Se non c'è, la ricerca riprende
         * da qui: un errore di lettura porterebbe alla fine del testo. */
        ParserState here = parser_save();
        next_token();
        linear_reals();
        if (syntax_error || is_char('^')) { parser_restore(here); syntax_error = NULL; continue; }
        letter = letter && letter != name ? -1 : name;
    }
    syntax_error = NULL;
    return letter;
}

/* Scrive in text, di size byte, la condizione "k non è nessuno dei count
 * valori di value[]", oppure "k è value[which]" se which non è negativo. */
static void parameter_case(const Frac *value, int count, int which, char *text, size_t size) {
    char number[64];
    for (int i = which < 0 ? 0 : which; i < (which < 0 ? count : which + 1); i++) {
        number[0] = 0;
        frac_latex(value[i], number, sizeof number);
        text_add(text, size, "%s%c %s %s", i && which < 0 ? " \\land " : "", letter_name[0], which < 0 ? "\\neq" : "=", number);
    }
}

/* Prova a dimostrare, smentire o risolvere l'enunciato formula, che ha un
 * parametro reale e parla di ranghi o di insiemi di soluzioni di sistemi
 * (vedi la testa del paragrafo). Svuota l'arena: i risultati di chiamate
 * precedenti non sono più validi.
 *
 * Ogni fatto viene discusso e sostituito nel testo dalla sua condizione sul
 * parametro; l'enunciato che resta lo decidono il capitolo 32, se ha ancora
 * dei determinanti, o le regole sui quantificatori. Una richiesta si risolve
 * in due tempi: i casi si scrivono, e l'enunciato che li afferma ripassa da
 * capo per questa stessa funzione. */
Verdict prove_parameter(const char *formula) {
    static _Thread_local char rewritten[4 * MAX_FORMULA], notes[PROOF_BYTES / 4], method[256], reason[768], answer[4 * MAX_FORMULA], reread[16 * MAX_FORMULA];
    static _Thread_local char cases[MAX_SPECIAL + 1][REQUEST_TEXT];
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, LINEAR_METHOD, NULL, NULL};
    MatrixStatement names;
    Frac special[MAX_SPECIAL];
    int k = parameter_of(formula), certified = 1;
    if (k < 0) { verdict.reason = "la discussione per casi è trattata con un solo parametro reale"; return verdict; }

    /* Ripartenza da zero, e le definizioni. Il parametro ha un valore solo
     * mentre si discute un fatto. */
    proof_reset();
    arena_used = arena_keep;
    failure = NULL;
    matrix_work = 0;
    placed_count = vector_name = letter_numbers = 0;
    discussion_facts = discussion_unproved = 0;
    rewritten[0] = discussion_certificates[0] = notes[0] = 0;
    letter_count = 1;
    letter_name[0] = k;
    letter_value[0] = frac_int(0);
    memset(&names, 0, sizeof names);
    matrix_start(formula);
    if (token.kind == T_LETTER && isupper(token.ch)) matrix_definitions(&names);

    /* Una richiesta: \forall k \in \mathbb{R}, e poi un insieme di soluzioni
     * o un rango, da soli. */
    ParserState start = parser_save();
    const char *start_consumed = consumed;
    if (is_command("forall") && !syntax_error) {
        LinearStatement st;
        MatrixKind kind;
        int values = -1;
        next_token();
        next_token();
        if (is_command("in")) next_token();
        linear_reals();
        const char *asked = token.start;
        if (!syntax_error && is_char(ESCAPED + '{') && linear_set_here()) {
            linear_fact(&st);
            if (!syntax_error && st.relation == LINEAR_ASKED && token.kind == T_END) {
                /* I casi di un sistema: le soluzioni in ogni valore speciale,
                 * e quelle generiche. */
                PMatrix a, b;
                linear_polynomials(&st, &names, &a, &b);
                GenericSolution s = generic_solve(a, b);
                values = failure ? 0 : up_rational_roots(s.where, special, MAX_SPECIAL);
                for (int i = 0; i < values && !failure; i++) {
                    Matrix at_a, at_b;
                    letter_value[0] = special[i];
                    Solution sol = linear_solution(&st, &names, &at_a, &at_b);
                    cases[i][0] = 0;
                    if (!failure) linear_answer(&st, sol, cases[i], sizeof cases[i]);
                }
                cases[values][0] = 0;
                if (!failure) generic_answer(&st, &s, cases[values], sizeof cases[values]);
            }
        } else if (!syntax_error && matrix_function(&kind) && kind == M_RANK) {
            MatrixNode *node = matrix_node(M_RANK, matrix_factor(), NULL);
            if (!syntax_error && token.kind == T_END) {
                /* I casi di un rango: i valori speciali in cui non è quello
                 * generico. Gli altri stanno nel caso generico. */
                PMatrix a;
                matrix_polynomials(node->a, &a);
                GenericRank g = generic_rank(a);
                Frac root[MAX_SPECIAL];
                int roots = failure ? 0 : up_rational_roots(g.minor, root, MAX_SPECIAL);
                values = 0;
                for (int i = 0; i < roots && !failure; i++) {
                    letter_value[0] = root[i];
                    MatrixValue at = matrix_eval(node, 0);
                    if (failure || at.number.num == g.rank) continue;
                    snprintf(cases[values], sizeof cases[values], "%lld", at.number.num);
                    special[values++] = root[i];
                }
                snprintf(cases[values], sizeof cases[values], "%d", g.rank);
            }
        }
        if (values >= 0) {
            /* La risposta, e l'enunciato che la afferma: ogni caso è una
             * condizione sul parametro e il valore che la richiesta ha lì. */
            const char *set = asked;
            int prefix = (int)(asked - formula), length = (int)strlen(asked);
            answer[0] = reread[0] = 0;
            if (!failure) {
                text_add(answer, sizeof answer, values ? "\\begin{cases} " : "");
                text_add(reread, sizeof reread, "%.*s(", prefix, formula);
                for (int i = 0; i <= values && !failure; i++) {
                    text_add(answer, sizeof answer, values ? "%s%s & " : "%s%s", i ? " \\\\ " : "", cases[i]);
                    text_add(reread, sizeof reread, values ? "%s(" : "%s", i ? " \\lor " : "");
                    if (values) {
                        parameter_case(special, values, i < values ? i : -1, answer, sizeof answer);
                        parameter_case(special, values, i < values ? i : -1, reread, sizeof reread);
                    }
                    text_add(reread, sizeof reread, values ? " \\land %.*s = %s)" : "%.*s = %s", length, set, cases[i]);
                }
                text_add(answer, sizeof answer, values ? " \\end{cases}" : "");
                text_add(reread, sizeof reread, ")");
            }
            if (failure || strlen(reread) >= sizeof rewritten) {
                verdict.reason = failure ? failure : "risultato troppo lungo da scrivere";
                return verdict;
            }
            Verdict stated = prove_parameter(reread);
            if (stated.outcome != PROVED) {
                char inner[400];
                if (stated.outcome == REFUTED) unjustified_steps++;
                snprintf(inner, sizeof inner, "%s", stated.reason ? stated.reason : "risulta falsa");
                snprintf(reason, sizeof reason, "i casi trovati, riletti come enunciato, non sono stati dimostrati: %s", inner);
                return (Verdict){stated.outcome == UNSUPPORTED ? UNSUPPORTED : NOT_PROVED, 0, 0, 0, reason, NULL, NULL, NULL, NULL, NULL};
            }
            stated.outcome = SOLVED;
            stated.detail = answer;
            return stated;
        }
        if (syntax_error || failure) { verdict.reason = syntax_error ? syntax_error : failure; return verdict; }
    }
    parser_restore(start);
    consumed = start_consumed;

    /* I fatti, uno dopo l'altro: ciò che sta tra l'uno e l'altro si copia
     * com'è. `copied` è dove la copia è arrivata; `defined` dice se il token
     * prima era un =, dopo il quale un insieme non è quello delle soluzioni
     * di un sistema (uses_linear_systems()). */
    const char *copied = formula;
    for (int defined = 0; token.kind != T_END && !syntax_error && !failure; ) {
        const char *from = token.start;
        Discussion d;
        MatrixKind kind;
        ParserState here = parser_save();
        const char *here_consumed = consumed;
        if (is_char(ESCAPED + '{') && !defined && linear_set_here()) {
            LinearStatement st;
            linear_fact(&st);
            if (!syntax_error && st.relation != LINEAR_EQ && st.relation != LINEAR_NEQ)
                syntax("con un parametro, un insieme di soluzioni dentro un enunciato si confronta con un insieme scritto: = \\emptyset, = \\{(1, 2)\\}");
            if (syntax_error) break;
            d = discuss_system(&st, &names);
        } else if (matrix_function(&kind) && kind == M_RANK) {
            RankFact fact;
            fact.rank = matrix_node(M_RANK, matrix_factor(), NULL);
            if (is_char('=')) fact.relation = MATRIX_EQ;
            else if (is_command("neq") || is_command("ne")) fact.relation = MATRIX_NEQ;
            else if (is_char('<')) fact.relation = MATRIX_LT;
            else if (is_char('>')) fact.relation = MATRIX_GT;
            else if (is_command("le") || is_command("leq")) fact.relation = MATRIX_LE;
            else if (is_command("ge") || is_command("geq")) fact.relation = MATRIX_GE;
            else syntax("con un parametro un rango sta a sinistra di un confronto con un numero: \\operatorname{rank} A = 2");
            next_token();
            fact.number = matrix_node(M_SCALAR, NULL, NULL);
            fact.number->scalar = parse_expr();
            if (syntax_error) break;
            d = discuss_rank(&fact);
        } else {
            parser_restore(here);
            consumed = here_consumed;
            defined = is_char('=');
            next_token();
            continue;
        }
        if (failure) break;
        if (d.generic < 0) { fail("nel caso generico l'insieme scritto ha un numero di vettori indipendenti diverso da quello dei parametri liberi delle soluzioni: "
                                  "con un parametro questo confronto non è ancora trattato"); break; }
        text_add(rewritten, sizeof rewritten, "%.*s", (int)(from - copied), copied);
        discussion_condition(&d, rewritten, sizeof rewritten);
        copied = consumed;
        defined = 0;
    }
    if (!syntax_error && !failure) text_add(rewritten, sizeof rewritten, "%s", copied);
    if (!syntax_error && !failure && !discussion_facts) fail(LETTER_CASES);
    if (!syntax_error && !failure && (strlen(rewritten) >= MAX_FORMULA || proof_length >= sizeof notes)) fail("enunciato troppo lungo, una volta discussi i suoi fatti");
    if (syntax_error || failure) {
        verdict.outcome = discussion_unproved && !syntax_error ? NOT_PROVED : UNSUPPORTED;
        verdict.reason = syntax_error ? syntax_error : failure;
        return verdict;
    }
    memcpy(notes, proof_text, proof_length + 1);
    letter_count = 0;

    /* h4. I valori speciali sono tutti: lo dimostra la tabella dei segni,
     * fatto per fatto. */
    for (int i = 0; i < discussion_facts; i++) {
        if (!discussion_roots[i][0]) continue;
        Verdict roots = prove_quantified(discussion_roots[i]);
        if (roots.outcome != PROVED) {
            snprintf(reason, sizeof reason, roots.outcome == REFUTED ? "un valore speciale del parametro è irrazionale: lì servirebbe il conto con i radicali, che non è ancora trattato"
                                                                     : "non riesco a stabilire che i valori speciali del parametro siano tutti");
            return (Verdict){UNSUPPORTED, 0, 0, 0, reason, NULL, NULL, NULL, NULL, NULL};
        }
        if (roots.certificate) text_add(discussion_certificates, sizeof discussion_certificates, "\n%s", roots.certificate);
        else certified = 0;
    }
    if (failure) { verdict.reason = failure; return verdict; }

    /* L'enunciato che resta, da capo. Se è deciso, il metodo dice anche
     * della discussione, e la dimostrazione la riporta in fondo. */
    verdict = uses_matrices(rewritten) ? prove_matrix(rewritten) : prove_quantified(rewritten);
    if (verdict.outcome != PROVED && verdict.outcome != REFUTED && verdict.outcome != SOLVED) return verdict;
    snprintf(method, sizeof method, "%s, dopo la discussione per casi sul parametro", verdict.method ? verdict.method : LINEAR_METHOD);
    verdict.method = method;
    proof_add(" The statement decided here is the given one with each fact about a rank or a set of solutions replaced by the condition on $%c$ that says "
              "where it holds: outside finitely many special values it is decided once, with polynomials in $%c$, and at each special value with numbers. "
              "%s The statement becomes $%s$.", k, k, notes, rewritten);
    if (proof_broken) return (Verdict){UNSUPPORTED, 0, 0, 0, "dimostrazione troppo lunga da scrivere", NULL, NULL, NULL, NULL, NULL};
    verdict.proof = proof_text;

    /* I certificati: quello dell'enunciato che resta, se c'è, e dopo di lui
     * quelli della discussione. Se manca, il motivo dice che cosa è
     * certificato lo stesso. */
    if (verdict.certificate && certified) {
        cert_add("\n%s", discussion_certificates);
        verdict.certificate = certificate_text;
        if (!certificate_broken) return verdict;
        verdict.reason = "i certificati sono troppo lunghi da scrivere insieme";
    }
    snprintf(reason, sizeof reason, "la discussione sul parametro ha i suoi certificati, verificati; %s%s%s",
             certified ? "l'enunciato che ne risulta no" : "che i valori speciali siano tutti, e l'enunciato che ne risulta, no",
             verdict.reason ? ", " : "", verdict.reason ? verdict.reason : "");
    verdict.reason = reason;
    verdict.certificate = NULL;
    return verdict;
}

/* 33i. IL VERDETTO */

/* Prova a dimostrare, smentire o risolvere l'enunciato su un sistema lineare
 * scritto in formula (vedi la testa del capitolo). Svuota l'arena: i
 * risultati di chiamate precedenti non sono più validi.
 *
 * Una richiesta si risolve in due tempi, come quelle del capitolo 32: si
 * trovano le soluzioni, le si scrive, e l'enunciato "insieme = soluzioni
 * scritte" passa da capo per questa stessa funzione, che lo rilegge e lo fa
 * certificare. Un errore nello scrivere le soluzioni cambia ciò che si
 * rilegge, e il verificatore lo respinge.
 *
 * Un enunciato che mette una lettera in \mathbb{R}, con un quantificatore o
 * con \{k \in \mathbb{R} \mid ...\}, ha un parametro: è di 33h. */
Verdict prove_linear(const char *formula) {
    static _Thread_local char answer[3 * MAX_FORMULA], reread[4 * MAX_FORMULA], problem[512];
    static _Thread_local LinearEvidence evidence;
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, LINEAR_METHOD, NULL, NULL};
    LinearStatement st;
    MatrixStatement names;
    Outcome outcome;
    int truth = 0;
    if (parameter_of(formula)) return prove_parameter(formula);

    /* Ripartenza da zero per il nuovo enunciato, e lettura. Nessuna lettera
     * ha un valore, e nessuna è il vettore incognito. */
    proof_reset();
    arena_used = arena_keep;
    failure = NULL;
    matrix_work = 0;
    letter_count = placed_count = vector_name = letter_numbers = 0;
    if (!parse_linear_statement(formula, &st, &names)) { verdict.reason = syntax_error; return verdict; }

    /* Una richiesta: le soluzioni, scritte, e l'enunciato che le afferma. */
    if (st.relation == LINEAR_ASKED) {
        Matrix a, b;
        Solution sol = linear_solution(&st, &names, &a, &b);
        answer[0] = 0;
        if (!failure) linear_answer(&st, sol, answer, sizeof answer);
        if (failure || strlen(formula) + strlen(answer) + 4 >= sizeof reread) {
            verdict.reason = failure ? failure : "risultato troppo lungo da scrivere";
            return verdict;
        }
        snprintf(reread, sizeof reread, "%s = %s", formula, answer);
        Verdict stated = prove_linear(reread);
        if (stated.outcome != PROVED) {
            char inner[256];
            if (stated.outcome == REFUTED) unjustified_steps++;
            snprintf(inner, sizeof inner, "%s", stated.reason ? stated.reason : "risulta falsa");
            snprintf(problem, sizeof problem, "le soluzioni trovate, rilette come enunciato, non sono state dimostrate: %s", inner);
            return (Verdict){NOT_PROVED, 0, 0, 0, problem, NULL, NULL, NULL, NULL, NULL};
        }
        stated.outcome = SOLVED;
        stated.detail = answer;
        return stated;
    }

    /* Un enunciato: che cosa dice, che cosa lo mostra, e il sì del
     * verificatore. */
    const char *trouble = linear_settle(&st, &names, &truth, &evidence, &outcome);
    if (trouble) return (Verdict){outcome, 0, 0, 0, trouble, NULL, NULL, outcome == UNSUPPORTED ? LINEAR_METHOD : NULL, NULL, NULL};
    verdict.outcome = truth ? PROVED : REFUTED;
    verdict.note = truth ? NULL : evidence.note;
    verdict.proof = proof_text;
    verdict.certificate = certificate_text;
    return verdict;
}

/* Ritorna 1 se formula scrive l'insieme delle soluzioni di un sistema
 * lineare, \{(x, y) \in \mathbb{R}^{2} \mid ...\} (31s): è un enunciato di
 * questo capitolo, e prove_core() lo manda qui. \{x \in \mathbb{R} \mid
 * ...\}, senza esponente, è un'equazione del capitolo 18 e non conta. E non
 * conta un insieme scritto subito dopo un segno =, R = \{(a, b) \in
 * \mathbb{R}^{2} \mid a - b \in \mathbb{Q}\}: è la definizione di una
 * relazione tra numeri (17j), mentre un insieme di soluzioni non segue mai
 * un = (31s). Senza questa eccezione tre enunciati dei test sugli insiemi
 * finivano qui, e uno vero risultava non supportato. Usa il lettore di
 * token del parser, e lascia il suo stato da reimpostare. */
int uses_linear_systems(const char *formula) {
    int found = 0, defined = 0;
    syntax_error = NULL;
    cursor = formula;
    for (next_token(); token.kind != T_END && !found; next_token()) {
        found = is_char(ESCAPED + '{') && !defined && linear_set_here();
        defined = is_char('=');
    }
    syntax_error = NULL;
    return found;
}
