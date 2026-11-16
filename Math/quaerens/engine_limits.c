/* MODULO engine_limits: limiti (capitolo 29).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_limits.h, e il
 * resto è static. */
#include "engine_limits.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"
#include "engine_intervals.h"
#include "engine_sign_tables.h"
#include "engine_sequences.h"

/* =============================================================================
 * 29. LIMITI
 * ============================================================================
 *
 * A che cosa serve. "Il limite di (1 - cos x)/x^2 per x che tende a 0 è
 * 1/2": l'enunciato arriva nella notazione di parse_limit_statement() (9i),
 * come affermazione da controllare, \lim_{x \to a} f = L, oppure come
 * richiesta, \lim_{x \to a} f, a cui si risponde RISOLTO con il valore. Il
 * metodo è uno solo, quello delle serie troncate con coefficienti esatti:
 * non c'è una formula per i limiti notevoli, una per de l'Hôpital, una per
 * le forme 1^\infty. Sono tutti casi della stessa aritmetica.
 *
 * 29a. IL PUNTO, I LATI, LA LETTERA t
 *
 * Ogni limite si porta a una lettera t > 0 che tende a 0: da destra di a si
 * scrive x = a + t, da sinistra x = a - t, a +\infty x = 1/t, a -\infty
 * x = -1/t. Un limite senza lato in un punto finito è fatto dei due limiti
 * da destra e da sinistra: esiste se tutti e due esistono e sono uguali, e
 * non esiste, dimostratamente, se sono diversi. Il limite è preso dentro il
 * campo di esistenza (29h): se da un lato la funzione non ha valori, conta
 * solo l'altro; se non ne ha da nessuno dei due, il punto non è di
 * accumulazione e il limite non ha senso.
 *
 * 29b. LE SERIE TRONCATE
 *
 * Una serie è una somma finita di termini c t^{k/D}, con c esatto, più un
 * resto O(t^{p/D}): una funzione che, per t piccolo, è al più una costante
 * per t^{p/D}. D, il denominatore comune degli esponenti, è 1 per i
 * polinomi e cresce con le radici (sqrt(t) = t^{1/2}: le serie di Puiseux).
 * Gli esponenti possono essere negativi: a +\infty x = t^{-1}. Il teorema
 * su cui tutto si regge è quello di Taylor con il resto di Peano: una
 * funzione con n derivate continue in u0 vale
 *
 *     g(u0 + w) = g(u0) + g'(u0) w + ... + g^{(n)}(u0) w^n / n! + o(w^n),
 *
 * e se w = O(t^v) con v > 0 il resto è O(t^{(n+1) v}). Somma e prodotto di
 * due serie sono una serie, con il resto che si calcola: (A + O(t^p))(B +
 * O(t^q)) = AB + O(t^{min(p + val B, q + val A)}), dove val è l'esponente
 * più basso. Il resto può anche non tendere a zero: O(t^0) è una funzione
 * limitata. Così sin(1/x) vicino a 0 è O(1), e x sin(1/x) è O(t): tende a
 * 0 anche se sin(1/x) non ha limite. Una serie esatta non ha resto. Quando
 * i coefficienti contengono la lettera L di 29d il resto vale a meno di una
 * potenza di L: O(t^{E}) vuol dire al più C t^{E} L^{m} (lim_logs).
 *
 * 29c. IL TERMINE PRINCIPALE E IL QUOZIENTE
 *
 * Il termine principale di una serie è il primo coefficiente diverso da
 * zero: se è c t^e, la funzione è c t^e (1 + o(1)), ha il segno di c, e
 * tende a +\infty o -\infty se e < 0, a c se e = 0, a 0 se e > 0. Decidere
 * che un coefficiente è zero è un conto esatto (il test di annullamento,
 * capitolo 12); che non lo è, e il suo segno, li dicono gli intervalli del
 * capitolo 24, e solo quando sono certi. Un coefficiente di cui non si sa
 * nulla ferma il conto: NON DIMOSTRATO. Se tutti i coefficienti noti sono
 * zero e il resto non tende a zero, si ricomincia con più termini: è ciò
 * che si fa a mano quando uno sviluppo al primo ordine "si cancella".
 * Dividere per una serie vuol dire 1/(c t^e (1 + u)) = c^{-1} t^{-e}
 * (1 - u + u^2 - ...), con u = O(t^{1/D}): l'ordine si sposta di -e. Il
 * limite di un quoziente è quindi il quoziente dei termini principali:
 * l'idea di de l'Hôpital, senza derivate.
 *
 * 29d. LA SCALA DEI LOGARITMI
 *
 * ln(c t^e (1 + u)) = ln c - e L + ln(1 + u), con L = ln(1/t), che tende a
 * +\infty più lentamente di ogni potenza di 1/t. I coefficienti possono
 * contenere la lettera L, anche al denominatore: x ln x da destra di 0 è
 * -L t, e tende a 0 perché t L tende a 0. Il termine principale di un
 * coefficiente c(L) è la sua potenza più alta in L: c(L) ~ k L^d. Un
 * esponenziale con L nel termine costante, e^{a + b L}, è e^a t^{-b} se b è
 * razionale: così x^x = e^{x ln x} e x^{1/x} = e^{(ln x)/x} hanno una serie.
 *
 * 29e. LE FUNZIONI
 *
 * Ogni funzione elementare entra con la sua serie di Taylor nel punto u0 a
 * cui tende l'argomento, con coefficienti esatti:
 *
 *     e^{u0 + w} = e^{u0} (1 + w + w^2/2 + ...),
 *     ln(c t^e (1 + w)) come in 29d, con ln(1 + w) = w - w^2/2 + ...,
 *     sin(u0 + w) = sin u0 cos w + cos u0 sin w, e il coseno allo stesso modo,
 *     arctan(u0 + w) = arctan u0 + arctan(w / (1 + u0 (u0 + w))),
 *     (c t^e (1 + w))^q = c^q t^{e q} (1 + q w + q (q - 1)/2 w^2 + ...);
 *
 * tangente e cotangente sono quozienti; le funzioni iperboliche arrivano
 * già scritte con queste (9h), e arcoseno e arcocoseno si riscrivono qui
 * con l'arcotangente (arcsin_by_arctan()). Quando l'argomento non
 * tende a un numero valgono regole a parte: e^{u} con u che tende a
 * -\infty è più piccolo di ogni potenza di t (una funzione "piatta": la
 * serie è 0 + O(t^n) per ogni n); arctan u con u che tende a +\infty o
 * -\infty è \pm \pi/2 - arctan(1/u); seno e coseno di qualunque cosa sono
 * O(1).
 *
 * 29f. LE FORME ESPONENZIALI
 *
 * f^g, con la variabile nell'esponente, vuol dire e^{g ln f}, ed è definita
 * solo dove f > 0: è il campo di esistenza dei libri, e lo stesso che usa
 * la tabella dei segni. Con un esponente numerico intero la potenza è un
 * prodotto, e la base può essere negativa; con uno razionale non intero la
 * base deve essere positiva, tranne che per le radici di indice dispari,
 * scritte con \sqrt[n]{}.
 *
 * 29g. L'ALGEBRA DEI LIMITI
 *
 * Quando una funzione non ha una serie (e^{1/x} da destra di 0 cresce più
 * di ogni potenza) resta il suo limite, e si va avanti con le regole dei
 * limiti sui numeri reali estesi: +\infty + c = +\infty, c / (0^{+}) =
 * \pm\infty con il segno di c, e^{+\infty} = +\infty, e^{-\infty} = 0^{+},
 * una funzione continua g in un numero L dà g(f) -> g(L). Una forma
 * indeterminata (\infty - \infty, 0 \cdot \infty, \infty / \infty) qui non
 * si scioglie: il verdetto è NON DIMOSTRATO.
 *
 * 29h. IL CAMPO DI ESISTENZA VICINO AL PUNTO
 *
 * Ogni operazione che ha una condizione la controlla sul termine
 * principale: un divisore con termine principale c t^e non nullo non si
 * annulla per t piccolo; un radicando, l'argomento di un logaritmo, la base
 * di f^g devono avere c > 0. Se c < 0 la funzione non ha valori da quel
 * lato, per nessun t piccolo: è un fatto, e lo si usa (29a). Un divisore
 * identicamente nullo dà lo stesso. In ogni altro caso dubbio il conto si
 * ferma.
 *
 * 29i. IL CONTROLLO CON I NUMERI
 *
 * Il risultato viene ricontrollato per un'altra strada: la funzione,
 * calcolata direttamente dall'albero con gli intervalli del capitolo 24
 * (node_range(), che non sa nulla di serie), nei punti x = a \pm 2^{-k}, o
 * x = \pm 2^{k} all'infinito. Da ogni lato il conto ha dato più del limite:
 * f - L ~ g(t), oppure f ~ g(t) per un limite infinito, con
 * g = c t^e L^d e^{G} il termine principale (29k: il fattore e^{G} è esatto,
 * e lo si calcola per intero con gli intervalli, L compresa). In quei punti
 * t = 2^{-k} e L = k ln 2; dopo la sostituzione di 29l t = 1/(k ln 2) e
 * L = ln(k ln 2), e i punti arrivano fino a k = 1000 perché L cresce
 * piano. Nei punti in cui l'intervallo è abbastanza stretto, il rapporto
 * (f - L)/g deve stare tra 1/16 e 16 (tende a 1); un punto in cui f o g
 * escono dai numeri della macchina (e^{x} per x = 2^{10}) non si usa. E g
 * deve andare dove va il limite: |g| deve scendere tra due valori lontani
 * di L (10^6 e 10^{12}, o 64 ln 2 e 256 ln 2 con un fattore e^{G}, che lì
 * resta tra i numeri della macchina) se il limite è finito, salire se è
 * infinito; lo si calcola dalla formula di g, in logaritmi, senza f. Che
 * cosa garantisce: un valore L sbagliato, un segno o un ordine sbagliati
 * fanno andare il rapporto a 0 o all'infinito, e lo si vede appena t è
 * abbastanza piccolo da lasciare indietro i termini successivi; due punti
 * consecutivi fuori dall'intervallo sono una contraddizione, il passo si
 * conta tra quelli non giustificati e il verdetto è NON DIMOSTRATO. Così
 * anche una g che va nella direzione sbagliata: è la regola che dal termine
 * principale ricava il limite (29c, 29k) a essere smentita, che il
 * rapporto da solo non vedrebbe (f ~ g anche se si sbaglia dove va g).
 * Che cosa non garantisce: nulla, da solo, perché un numero finito di
 * valori non decide un limite; e un errore più piccolo di un fattore 16 nel
 * coefficiente principale, o nascosto da una convergenza lentissima, passa.
 * Per questo il controllo conferma e non dimostra: senza almeno un punto
 * che confermi il verdetto è NON DIMOSTRATO. Quando di f - L non si conosce
 * un termine principale ma solo il resto, O(t^{E}), o il fatto che è più
 * piccolo di ogni potenza (una funzione piatta, un fattore e^{G} che va a
 * zero), si chiede |f - L| <= 16 (1 + |L|) t^{B} nell'ultimo punto
 * abbastanza preciso, con B = min(E, 1), o B = 4 se è piatta. Quando il
 * limite viene dall'algebra dei limiti (29g) non c'è nemmeno quello, e si
 * chiede solo che nell'ultimo punto utile f stia vicino a L, o abbia il
 * segno dell'infinito. Lo stesso controllo vale per il campo di esistenza:
 * un lato dichiarato senza valori deve risultare senza valori nei punti più
 * vicini al punto, e viceversa.
 *
 * 29j. IL VERDETTO E LA RISPOSTA RILETTA
 *
 * \lim f = L è DIMOSTRATO se il limite calcolato è L, esattamente; FALSO
 * solo se il limite è stato calcolato (o la sua non esistenza dimostrata,
 * con due limiti da destra e da sinistra diversi) ed è certamente diverso
 * da L; altrimenti NON DIMOSTRATO. Il valore scritto, nella dimostrazione e
 * nella risposta a una richiesta, viene riletto dal testo con il lettore
 * del capitolo 9 e confrontato con quello calcolato, come le soluzioni
 * della tabella dei segni.
 *
 * Il limite di una successione, \lim_{n \to +\infty} a_n, si calcola come
 * quello della funzione con n reale: se questo esiste la successione ha lo
 * stesso limite (teorema ponte), ma se non esiste non si può dire nulla.
 *
 * 29k. LA SCALA DELLE CRESCITE
 *
 * e^{x} / x^{5} a +\infty è \infty / \infty per l'algebra dei limiti, e
 * e^{1/t} non ha una serie in t. Lo si scrive allora con un fattore in più:
 * una funzione è e^{G} S, con S una serie come in 29b e G un esponente
 * esatto, una somma finita di termini g_i(L) t^{-k_i} con k_i > 0 e i
 * coefficienti g_i frazioni di polinomi nelle costanti e in L. e^{x} è
 * e^{t^{-1}} 1, x^{x} 2^{-x} = e^{x ln x - x ln 2} è e^{(L - ln 2) t^{-1}} 1,
 * e^{1/x} da destra di 0 è e^{t^{-1}} 1. È la scala delle crescite dei libri,
 * c x^{a} (\ln x)^{b} e^{P(x)}, con il confronto fattore per fattore: un
 * pezzo ristretto del metodo di Gruntz (D. Gruntz, "On computing limits in a
 * symbolic manipulation system", tesi, ETH Zurigo 1996), che a sua volta
 * viene dai campi di Hardy (G. H. Hardy, "Orders of infinity", 1910). I
 * fatti su cui si regge, con t -> 0^{+} e L = ln(1/t):
 *
 *   (a) L cresce meno di ogni potenza: t^{eps} L^{d} -> 0 per ogni eps > 0
 *       e ogni d (con s = L, t^{eps} L^{d} = e^{-eps s} s^{d}, e
 *       l'esponenziale batte ogni potenza di s);
 *   (b) se H = lambda(L) t^{-k} (1 + o(1)) con k > 0 e lambda(L) ~ c L^{j},
 *       c != 0, allora H / L -> +\infty o -\infty con il segno di c, perché
 *       t^{-k} L^{j - 1} -> +\infty per (a). Quindi per ogni e e d
 *
 *           e^{H} t^{e} L^{d} = exp(H - e L + d ln L) -> +\infty oppure 0,
 *
 *       perché H - e L + d ln L = H (1 + o(1)): e^{H} sta sopra o sotto ogni
 *       potenza di t e di L. È il confronto "gli esponenziali battono le
 *       potenze, che battono i logaritmi" dei libri;
 *   (c) somma: se G1 - G2 = H come in (b) con c > 0, allora
 *       e^{G1} S1 + e^{G2} S2 = e^{G1} (S1 + e^{-H} S2), ed e^{-H} S2 è più
 *       piccola di ogni potenza di t (b): è una funzione piatta (29e). Se
 *       G1 - G2 è esattamente zero (test di annullamento) le serie si
 *       sommano; se non si sa che segno ha, il conto si ferma;
 *   (d) prodotto e quoziente: e^{G1} S1 e^{G2} S2 = e^{G1 + G2} S1 S2, e
 *       1 / (e^{G} S) = e^{-G} / S;
 *   (e) potenze e logaritmi: (e^{G} S)^q = e^{q G} S^q e
 *       ln(e^{G} S) = G + ln S, perché e^{G} > 0;
 *   (f) l'esponenziale: se v = N + c(L) + P, con N i termini di esponente
 *       negativo (esatti, perché il resto di v tende a zero), c(L) il
 *       termine costante e P -> 0, allora e^{v} = e^{N} e^{c(L)} e^{P}:
 *       e^{N} è il fattore nuovo, gli altri due li sa già scrivere 29d. Se
 *       v ha già un fattore e^{G}, e^{v} sale di un piano (e^{e^{x}}) e si
 *       sa solo il suo limite, come in 29g.
 *
 * Il limite di e^{G} S: G ha un termine principale c t^{-k}; se c > 0 la
 * funzione tende all'infinito con il segno del termine principale di S, se
 * c < 0 tende a 0. Le funzioni che non sanno trattare il fattore (seno,
 * coseno, arcotangente) lo ricevono come lo vedeva l'algebra dei limiti:
 * un infinito, o una funzione piatta (value_plain()).
 *
 * 29l. SALIRE DI UN PIANO: x = e^{1/t}
 *
 * ln x / ln ln x a +\infty chiederebbe il logaritmo di L, che i coefficienti
 * non hanno. È il "moving up" di Gruntz: con x = e^{1/t} ogni ln x diventa
 * 1/t e ogni ln ln x diventa L, e i logaritmi scendono di un piano. La
 * sostituzione è lecita perché t -> e^{1/t} è una biiezione crescente da
 * (0, +\infty) a (1, +\infty), e t -> 0^{+} se e solo se x -> +\infty:
 * allora lim_{x -> +\infty} f(x) = lim_{t -> 0^{+}} f(e^{1/t}), nei due versi.
 * Allo stesso modo x = e^{-1/t} da destra di 0, x = -e^{1/t} a -\infty,
 * x = -e^{-1/t} da sinistra di 0; in un punto a diverso da zero x - a non
 * avrebbe una forma sola, e la sostituzione non si fa. La si prova solo
 * quando quella di 29a non arriva a un limite: con x = e^{1/t} un polinomio
 * come (x + 1)^2 - x^2 perde i termini piccoli (c), e non si scioglie più.
 *
 * Che cosa manca. Le stime (8 + sin^2 x \ge 8) per divergenze con
 * oscillazioni; due successioni per dimostrare che un limite in +\infty non
 * esiste; i parametri; le funzioni definite a pezzi; un esponenziale di un
 * esponenziale come fattore (e^{e^{x}} - e^{e^{x} - x}); i logaritmi annidati
 * più di una volta (ln ln ln x), che chiederebbero di salire di due piani.
 *
 * 29n. IL CERTIFICATO
 *
 * Il verdetto va a checker.c come certificato: l'enunciato, la sostituzione
 * e la precisione di ogni lato. Il verificatore rifà gli sviluppi con la sua
 * aritmetica e le sue regole (il suo capitolo 14), e il verdetto vuole che
 * lo accetti; vedi limit_certify().
 */

/* Il nome interno della lettera L = ln(1/t) (29d): non è un carattere. */
#define VAR_LOG_SCALE 5000

/* L'esponente "infinito" (29b): il resto di una serie esatta, o di una
 * funzione piatta, è O(t^{SERIES_FLAT}). Le somme di esponenti si fermano lì
 * (series_plus()), così non traboccano. */
#define SERIES_FLAT 1000000

#define MAX_SERIES_TERMS 48  /* coefficienti noti, al più, in una serie */
#define MAX_SERIES_DEN 24    /* denominatore massimo degli esponenti di una serie */
#define MAX_TAYLOR 20        /* termini di una serie di Taylor: 1/20! sta ancora nei razionali */
#define LIMIT_SAMPLES 60     /* punti del controllo con i numeri, t = 2^{-k} con k fino a 60 */
#define MOVED_SAMPLES 1000   /* lo stesso dopo la sostituzione di 29l: k fino a 1000, di 4 in 4 */

/* Le precisioni provate una dopo l'altra (29c): si sviluppa fino a t^4, poi
 * fino a t^8, poi fino a t^16, finché il termine principale non si trova. */
static const int series_goals[] = {4, 8, 16};

/* Una serie troncata (29b): la somma dei count coefficienti coef[i] per
 * t^{(low + i)/den}, più un resto O(t^{end/den}). Gli esponenti tra
 * low + count ed end hanno coefficiente zero.
 *
 * Invarianti: den >= 1; low + count <= end; se exact è 1 il resto non c'è ed
 * end vale SERIES_FLAT. Una funzione piatta ha count = 0, end = SERIES_FLAT
 * ed exact = 0; una funzione solo limitata ha count = 0 ed end = 0. I
 * coefficienti sono frazioni di polinomi nelle costanti (pi, e, logaritmi
 * di primi, radici) e nella lettera L; stanno nell'arena, come i Rat. */
typedef struct {
    int den;      /* D: gli esponenti sono multipli di 1/D */
    int low;      /* esponente, in unità 1/D, di coef[0] */
    int count;    /* coefficienti noti */
    int end;      /* esponente del resto, in unità 1/D */
    int exact;    /* 1 se la serie è una somma finita, senza resto */
    Rat *coef;
} Series;

/* Che cosa dice di un coefficiente c(L) il suo termine principale (29d). */
typedef struct {
    int known;      /* 1 se si sa se è zero e, se non lo è, il segno */
    int zero;       /* 1 se c(L) è zero */
    int side;       /* il segno di c(L) per L grande: +1 o -1 */
    Frac degree;    /* c(L) ~ value L^degree */
    Rat value;      /* il coefficiente della potenza più alta, senza L */
} Lead;

/* Ciò che il conto sa di una funzione vicino al punto, da un lato (29a):
 *   V_SERIES     la sua serie troncata;
 *   V_LIMIT      solo il suo limite (29g): +\infty, -\infty o un numero;
 *   V_UNDEFINED  che non ha valori in tutto un intorno da quel lato (29h);
 *   V_UNKNOWN    niente: il conto non sa andare avanti, e why dice perché. */
typedef enum { V_SERIES, V_LIMIT, V_UNDEFINED, V_UNKNOWN } ValueKind;

/* Una funzione vicino al punto, con ciò che se ne sa (vedi ValueKind). Per
 * V_SERIES la funzione è e^{G} S (29k), con S = series e G = growth; senza
 * fattore growth ha count = 0.
 * Invariante: growth è esatta, con i soli esponenti negativi; se ha dei
 * termini, series non è esattamente zero (value_grown()). */
typedef struct {
    ValueKind kind;
    Series series;    /* V_SERIES: S */
    int infinite;     /* V_LIMIT: +1 per +\infty, -1 per -\infty, 0 per un numero */
    Rat value;        /* V_LIMIT finito: il numero, senza la lettera L */
    int approach;     /* V_LIMIT finito: +1 se la funzione sta sopra il numero, -1 sotto, 0 se non si sa */
    int positive;     /* 1 se la funzione è certamente positiva vicino al punto */
    const char *why;  /* V_UNDEFINED, V_UNKNOWN: perché, in italiano */
    Series growth;    /* V_SERIES: l'esponente G del fattore e^{G} (29k) */
} Value;

/* Il motivo con cui un conto chiede più termini (29c): ha un nome perché
 * limit_side() lo riconosce e ricomincia con una precisione più alta. */
static const char *const NEEDS_PRECISION = "lo sviluppo, anche con più termini, non mostra un termine principale";

/* Il limite in corso: la variabile, il punto (finito, o +1 / -1 per
 * +\infty e -\infty), il lato, la precisione cercata (un esponente intero
 * di t), l'atomo della lettera L, se una potenza f^g è stata letta come
 * e^{g ln f} (lo dice la dimostrazione), e se la variabile è scritta con la
 * sostituzione di 29l, x = \pm e^{\pm 1/t}. */
static int lim_x, lim_infinity, lim_side, lim_goal, lim_ell, lim_exponential, lim_moved;
static Rat lim_point;

/* 1 se il conto in corso ha scritto la lettera L in un coefficiente (lo fa
 * solo value_ln()). Da quel momento un resto "O(t^{E})" vale a meno di una
 * potenza di L: un O(1) moltiplicato per -L, come \sin\frac{1}{x} \ln x, è
 * scritto O(t^{0}) ma non è limitato. Per i limiti non importa (t^{E} L^{m}
 * tende a zero per ogni E > 0), per e^{O(1)} sì: vedi value_exp(). */
static int lim_logs;

/* Il valore di L durante il controllo con i numeri (29i), per gli intervalli
 * dei coefficienti che la contengono; "non so" in ogni altro momento, perché
 * L è una lettera e non un numero. */
static Range lim_ell_range = {1, -1};

/* Somma di due esponenti: SERIES_FLAT se uno dei due lo è. Due esponenti
 * veri non devono mai arrivare vicino a SERIES_FLAT, che vuol dire "più di
 * ogni potenza": t^{2 SERIES_FLAT} preso per piatto, moltiplicato per
 * t^{-2 SERIES_FLAT}, darebbe 0 invece di 1. Oltre MAX_EXPONENT il conto
 * fallisce. */
#define MAX_EXPONENT (SERIES_FLAT / 16)
static int series_plus(int a, int b) {
    if (a >= SERIES_FLAT || b >= SERIES_FLAT) return SERIES_FLAT;
    long long sum = (long long)a + b;
    if (sum > MAX_EXPONENT || sum < -MAX_EXPONENT) { fail("esponenti troppo grandi in uno sviluppo"); return 0; }
    return (int)sum;
}

/* Ritorna una serie con den, low, count, end ed exact dati e i coefficienti
 * tutti zero. */
static Series series_make(int den, int low, int count, int end, int exact) {
    Series s = {den, low, count, end, exact, NULL};
    Rat zero = {poly_const(num_int(0)), poly_const(num_int(1))};
    if (count > 0) s.coef = arena_alloc((size_t)count * sizeof(Rat));
    if (!s.coef) s.count = 0;
    for (int i = 0; i < s.count; i++) s.coef[i] = zero;
    return s;
}

/* Ritorna la costante c come serie esatta. */
static Series series_const(Rat c) {
    Series s = series_make(1, 0, c.num.count ? 1 : 0, SERIES_FLAT, 1);
    if (s.count) s.coef[0] = c;
    return s;
}

/* Ritorna la funzione O(1), limitata e niente di più (29b). */
static Series series_bounded(void) { return series_make(1, 0, 0, 0, 0); }

/* Ritorna 1 se il Rat r contiene la lettera L. Solo come fattore di un
 * monomio: il capitolo non crea atomi con L dentro (vedi constant_ln()). */
static int rat_has_ell(Rat r) {
    for (int side = 0; side < 2; side++) {
        Poly p = side ? r.den : r.num;
        for (int i = 0; i < p.count; i++)
            if (mono_exponent(&p.term[i].mono, lim_ell).num != 0) return 1;
    }
    return 0;
}

/* Toglie da s i coefficienti iniziali scritti senza termini, e da una serie
 * esatta anche quelli finali: non cambia la funzione. */
static Series series_trim(Series s) {
    while (s.count > 0 && s.coef[0].num.count == 0) { s.coef++; s.count--; s.low++; }
    while (s.exact && s.count > 0 && s.coef[s.count - 1].num.count == 0) s.count--;
    if (s.count == 0) s.low = s.exact ? 0 : s.end;
    return s;
}

/* Ritorna s con il resto spostato a O(t^{end/den}), se end è più basso: ciò
 * che sta oltre si dimentica, e una serie esatta smette di esserlo.
 * Dimenticare è sempre lecito. */
static Series series_cut(Series s, int end) {
    if (end >= s.end) return s;
    s.exact = 0;
    s.end = end;
    if (s.low + s.count > end) s.count = end > s.low ? end - s.low : 0;
    if (s.count == 0) s.low = end;
    return s;
}

/* Ritorna s scritta con il denominatore den, multiplo del suo. */
static Series series_rescale(Series s, int den) {
    int k = den / s.den;
    if (k == 1) return s;
    int count = s.count ? (s.count - 1) * k + 1 : 0;
    Series r = series_make(den, s.low < SERIES_FLAT ? series_plus(s.low * k, 0) : SERIES_FLAT, count,
                           s.end < SERIES_FLAT ? series_plus(s.end * k, 0) : SERIES_FLAT, s.exact);
    for (int i = 0; i < s.count && r.count; i++) r.coef[i * k] = s.coef[i];
    return r;
}

/* Porta a e b allo stesso denominatore. Ritorna 0 se sarebbe troppo grande. */
static int series_common(Series *a, Series *b) {
    long long den = lcm_small(a->den, b->den);
    if (den > MAX_SERIES_DEN) return 0;
    *a = series_rescale(*a, (int)den);
    *b = series_rescale(*b, (int)den);
    return 1;
}

/* Ritorna s moltiplicata per la costante c. */
static Series series_scale(Series s, Rat c) {
    if (c.num.count == 0) return series_const(c);
    Series r = series_make(s.den, s.low, s.count, s.end, s.exact);
    for (int i = 0; i < r.count; i++) r.coef[i] = rat_mul(s.coef[i], c);
    return series_trim(r);
}

/* Ritorna s moltiplicata per t^{shift/den}. */
static Series series_shift(Series s, int shift) {
    s.low = series_plus(s.low, shift);
    s.end = series_plus(s.end, shift);
    return s;
}

/* Ritorna a + b, oppure a - b se subtract è diverso da zero; *ok diventa 0
 * se i denominatori non si possono mettere insieme. */
static Series series_add(Series a, Series b, int subtract, int *ok) {
    *ok = series_common(&a, &b);
    if (!*ok) return a;
    int end = a.end < b.end ? a.end : b.end, exact = a.exact && b.exact, low = SERIES_FLAT, top = -SERIES_FLAT;
    if (a.count) { low = a.low; top = a.low + a.count; }
    if (b.count && b.low < low) low = b.low;
    if (b.count && b.low + b.count > top) top = b.low + b.count;
    if (top > end) top = end;
    if (low >= top) low = top = end;
    if (top - low > MAX_SERIES_TERMS) { top = low + MAX_SERIES_TERMS; end = top; exact = 0; }
    Series r = series_make(a.den, low, top - low, end, exact);
    for (int i = 0; i < r.count; i++) {
        int e = low + i, ia = e - a.low, ib = e - b.low;
        Rat sum = ia >= 0 && ia < a.count ? a.coef[ia] : r.coef[i];
        if (ib >= 0 && ib < b.count) sum = rat_add(sum, b.coef[ib], subtract);
        r.coef[i] = sum;
    }
    return series_trim(r);
}

/* Ritorna a b (29b); *ok come per series_add(). */
static Series series_mul(Series a, Series b, int *ok) {
    *ok = series_common(&a, &b);
    if (!*ok) return a;
    if ((a.exact && a.count == 0) || (b.exact && b.count == 0)) return series_const(rat_int(0));

    /* Le valutazioni, o il resto dove non si conosce nulla, e il resto del
     * prodotto. */
    int va = a.count ? a.low : a.end, vb = b.count ? b.low : b.end;
    int end = series_plus(va, b.end), other = series_plus(vb, a.end), exact = a.exact && b.exact;
    if (other < end) end = other;
    int low = series_plus(va, vb), top = a.count && b.count ? a.low + a.count - 1 + b.low + b.count : low;
    if (top > end) top = end;
    if (low > top) low = top;
    if (top - low > MAX_SERIES_TERMS) { top = low + MAX_SERIES_TERMS; end = top; exact = 0; }
    Series r = series_make(a.den, low, top - low, end, exact);
    for (int i = 0; i < a.count; i++) {
        if (a.coef[i].num.count == 0) continue;
        for (int j = 0; j < b.count; j++) {
            int k = a.low + i + b.low + j - low;
            if (k >= r.count) break;
            if (b.coef[j].num.count) r.coef[k] = rat_add(r.coef[k], rat_mul(a.coef[i], b.coef[j]), 0);
        }
    }
    return series_trim(r);
}

/* LE COSTANTI
 *
 * I coefficienti delle serie sono numeri esatti scritti come frazioni di
 * polinomi negli atomi del capitolo 4: pi, la lettera e (qui sempre il
 * numero di Nepero), i primi con un esponente razionale (le radici), i
 * logaritmi, le arcotangenti, gli esponenziali complessi e^{i theta} con cui
 * il capitolo 11 scrive seni e coseni. Servono due cose: il segno di un
 * coefficiente, che dà un intervallo, e i valori delle funzioni nei punti
 * costanti, scritti in modo che lo stesso numero arrivi sempre alla stessa
 * forma: e^{1/2} è un monomio con la lettera e elevata a 1/2, ln e è 1,
 * e^{q ln p} è p^q. Due scritture diverse dello stesso numero non sono un
 * errore (il test di annullamento direbbe "non so"), solo un limite in meno
 * dimostrato. */

/* Un numero complesso noto a meno di un errore: le due parti, ognuna un
 * intervallo del capitolo 24. Serve per i coefficienti che contengono
 * e^{i theta}, che sono numeri reali scritti con numeri complessi. */
typedef struct {
    Range re, im;
} Pair;

/* Prodotto di due numeri complessi: (a + b i)(c + d i). */
static Pair pair_mul(Pair a, Pair b) {
    return (Pair){range_sub(range_mul(a.re, b.re), range_mul(a.im, b.im)), range_add(range_mul(a.re, b.im), range_mul(a.im, b.re))};
}

/* Il numero reale r come numero complesso. */
static Pair pair_real(Range r) { return (Pair){r, {0, 0}}; }

/* Ritorna il quadrato di r, che non è negativo anche quando r contiene lo
 * zero (il prodotto di intervalli lo farebbe scendere sotto). */
static Range range_square(Range r) {
    if (!range_known(r)) return r;
    if (r.low >= 0 || r.high <= 0) return range_mul(r, r);
    double top = -r.low > r.high ? -r.low : r.high;
    return range_wide(0, top * top);
}

/* Ritorna il modulo del numero complesso a. */
static Range pair_modulus(Pair a) {
    if (range_known(a.im) && a.im.low == 0 && a.im.high == 0) return range_known(a.re) && a.re.low >= 0 ? a.re : range_known(a.re) && a.re.high <= 0 ? range_neg(a.re) : range_sqrt(range_square(a.re));
    return range_sqrt(range_add(range_square(a.re), range_square(a.im)));
}

/* Ritorna la parte reale di a, che deve essere un numero reale scritto con
 * numeri complessi: "non so" se la parte immaginaria non può essere zero. */
static Range pair_real_part(Pair a) {
    return range_known(a.im) && a.im.low <= 0 && a.im.high >= 0 ? a.re : range_none();
}

/* Prototipi in avanti inevitabili: un atomo può avere per base un polinomio
 * o per esponente un monomio, fatti di atomi. poly_pair() ritorna il valore
 * del polinomio p di costanti; mono_real_range() un intervallo per il valore
 * reale del monomio m, di soli atomi reali (l'esponente di un atomo e^{i M}). */
static Pair poly_pair(Poly p);
static Range mono_real_range(const Mono *m);

/* Ritorna il valore dell'atomo elevato a e, come numero complesso, o "non
 * so". La lettera L ha un valore solo durante il controllo con i numeri
 * (lim_ell_range); altrimenti il suo intervallo è "non so". */
static Pair atom_pair(int atom, Frac e) {
    const Atom *a = &atoms[atom];
    Pair none = {range_none(), range_none()};
    Range base, power = range_ratio(e.num, e.den);

    /* e^{i M} elevato a e: l'angolo e M, il punto (cos, sin). */
    if (a->kind == ATOM_POW && a->base == BASE_EI) {
        Range sine, cosine;
        range_sin_cos(range_mul(power, mono_real_range(&a->exponent)), &sine, &cosine);
        return (Pair){cosine, sine};
    }
    switch (a->kind) {
    case ATOM_VAR:
        if (a->id == VAR_PI) base = range_pi();
        else if (a->id == 'e') base = range_exp_at(1);
        else if (a->id == VAR_LOG_SCALE && range_known(lim_ell_range)) base = lim_ell_range;
        else return none;
        break;
    case ATOM_POW:
        base = a->base == BASE_PRIME ? range_ratio(a->id, 1)
             : a->base == BASE_ATOM ? pair_real_part(atom_pair((int)a->id, frac_int(1)))
             : pair_real_part(poly_pair(base_polys[a->id]));
        if (a->exponent.count) power = range_mul(power, mono_real_range(&a->exponent));
        if (a->exponent.count || e.den != 1) return pair_real(range_exp(range_mul(power, range_ln(base))));
        break;
    case ATOM_LN:
        base = range_ln(a->base == BASE_PRIME ? range_ratio(a->id, 1)
                        : a->base == BASE_ATOM ? pair_modulus(atom_pair((int)a->id, frac_int(1)))
                        : pair_modulus(poly_pair(base_polys[a->id])));
        break;
    case ATOM_ATAN:
        base = range_atan(range_div(pair_real_part(poly_pair(atan_args[a->id].num)), pair_real_part(poly_pair(atan_args[a->id].den))));
        break;
    default:
        return none;
    }
    if (e.den == 1) return pair_real(range_power(base, e.num));
    return pair_real(range_exp(range_mul(power, range_ln(base))));
}

static Range mono_real_range(const Mono *m) {
    Pair product = pair_real((Range){1, 1});
    for (int i = 0; i < m->count; i++) product = pair_mul(product, atom_pair(m->factor[i].atom, m->factor[i].exp));
    return range_known(product.im) && product.im.low <= 0 && product.im.high >= 0 ? product.re : range_none();
}

/* Ritorna il valore del polinomio p di costanti, come numero complesso. */
static Pair poly_pair(Poly p) {
    Pair sum = pair_real((Range){0, 0});
    for (int t = 0; t < p.count; t++) {
        const Term *term = &p.term[t];
        Pair product = {range_ratio(term->coef.re.num, term->coef.re.den), range_ratio(term->coef.im.num, term->coef.im.den)};
        for (int f = 0; f < term->mono.count; f++) product = pair_mul(product, atom_pair(term->mono.factor[f].atom, term->mono.factor[f].exp));
        sum = (Pair){range_add(sum.re, product.re), range_add(sum.im, product.im)};
    }
    return sum;
}

/* Ritorna un intervallo che contiene la costante reale c, o "non so". Il
 * quoziente di due numeri complessi è n conj(d) / |d|^2; la parte
 * immaginaria deve poter essere zero, perché c è reale: se non può, il
 * numero non è quello che si crede, e la risposta è "non so". */
Range constant_range(Rat c) {
    Pair n = poly_pair(c.num), d = poly_pair(c.den);
    Range size = range_add(range_square(d.re), range_square(d.im));
    Range re = range_div(range_add(range_mul(n.re, d.re), range_mul(n.im, d.im)), size);
    Range im = range_div(range_sub(range_mul(n.im, d.re), range_mul(n.re, d.im)), size);
    if (!range_known(im) || im.low > 0 || im.high < 0) return range_none();
    return re;
}

/* Il segno della costante c, senza la lettera L. Ritorna 0 se c è zero (il
 * test di annullamento, esatto), 1 se il segno è certo e lo mette in *side,
 * -1 se non si sa. Un errore di calcolo durante il test vale "non so". */
static int constant_sign(Rat c, int *side) {
    const char *saved = failure;
    int zero = c.num.count == 0 || poly_vanishes(c.num);
    if (failure != saved) { failure = saved; return -1; }
    if (zero) return 0;
    return range_side(constant_range(c), side) ? 1 : -1;
}

/* Della parte di p con la potenza più alta della lettera L mette in *degree
 * l'esponente, in *lead il coefficiente senza L e in *side il suo segno. Le
 * potenze più alte il cui coefficiente è zero (test esatto) si saltano.
 * Ritorna 1 se ci riesce, 0 se p è zero, -1 se un segno non si sa. */
static int poly_top(Poly p, Frac *degree, Poly *lead, int *side) {
    while (p.count > 0) {
        Frac top = mono_exponent(&p.term[0].mono, lim_ell);
        for (int i = 1; i < p.count; i++) {
            Frac e = mono_exponent(&p.term[i].mono, lim_ell);
            if (frac_cmp(e, top) > 0) top = e;
        }
        Term *high = terms_alloc(p.count), *low = terms_alloc(p.count);
        if (!high || !low) return -1;
        int highs = 0, lows = 0;
        for (int i = 0; i < p.count; i++) {
            Term t = p.term[i];
            if (frac_cmp(mono_exponent(&t.mono, lim_ell), top) != 0) { low[lows++] = t; continue; }
            t.mono = mono_with_exponent(&t.mono, lim_ell, frac_int(0));
            high[highs++] = t;
        }
        Poly group = poly_finish(high, p.count, highs);
        int known = constant_sign((Rat){group, poly_const(num_int(1))}, side);
        if (known < 0) return -1;
        if (known > 0) { *degree = top; *lead = group; return 1; }
        p = poly_finish(low, p.count, lows);
    }
    return 0;
}

/* Il termine principale del coefficiente c (29d), in *out. */
static Lead coefficient_lead(Rat c) {
    Lead out = {0, 0, 0, {0, 1}, {{0, NULL}, {0, NULL}}};
    Frac above, below;
    Poly top, bottom;
    int up, down;
    int found = poly_top(c.num, &above, &top, &up);
    if (found == 0) { out.known = out.zero = 1; return out; }
    if (found < 0 || poly_top(c.den, &below, &bottom, &down) <= 0) return out;
    out.known = 1;
    out.side = up * down;
    out.degree = frac_add(above, frac_neg(below));
    out.value = rat_make(top, bottom);
    return out;
}

/* Toglie da *s i coefficienti iniziali che sono zero (test esatto) e mette
 * in *lead il termine principale del primo che resta. Ritorna 1 se quel
 * coefficiente c'è e non è zero, 0 se non si sa se lo sia, -1 se non resta
 * nessun coefficiente noto. */
static int series_settle(Series *s, Lead *lead) {
    for (;;) {
        *s = series_trim(*s);
        if (s->count == 0) return -1;
        *lead = coefficient_lead(s->coef[0]);
        if (!lead->known) return 0;
        if (!lead->zero) return 1;
        s->coef[0] = (Rat){poly_const(num_int(0)), poly_const(num_int(1))};
    }
}

/* Ritorna 1 se l'atomo è certamente positivo: pi, e, un primo con un
 * esponente, il logaritmo di un primo, la lettera L (che è ln(1/t), con
 * t < 1), oppure un atomo il cui intervallo è positivo. */
static int atom_positive(int atom) {
    const Atom *a = &atoms[atom];
    int side;
    if (a->kind == ATOM_VAR) return a->id == VAR_PI || a->id == 'e' || a->id == VAR_LOG_SCALE;
    if ((a->kind == ATOM_POW || a->kind == ATOM_LN) && a->base == BASE_PRIME) return 1;
    return range_side(atom_pair(atom, frac_int(1)).re, &side) && side > 0 && atom_pair(atom, frac_int(1)).im.low == 0;
}

/* Il logaritmo naturale di |t|, per un solo termine t senza unità
 * immaginaria: ln|r| + somma di e_i ln|a_i| per il coefficiente r e gli
 * atomi a_i^{e_i}. Le regole che lo tengono in forma unica: ln e = 1,
 * |e^{i theta}| = 1, ln(e^{M}) = M, e ln|u^q| = q ln|u|. Ritorna 0 se t non
 * ha questa forma. */
static int term_log(Term t, Rat *out) {
    if (t.coef.im.num != 0 || t.coef.re.num == 0) return 0;
    Frac size = t.coef.re.num < 0 ? frac_neg(t.coef.re) : t.coef.re;
    Rat total = logarithm(rat_frac(size));
    for (int i = 0; i < t.mono.count; i++) {
        int atom = t.mono.factor[i].atom;
        const Atom *a = &atoms[atom];
        Rat piece;
        if (a->kind == ATOM_VAR && a->id == 'e') piece = rat_int(1);
        else if (a->kind == ATOM_POW && a->base == BASE_EI) continue;
        else if (a->kind == ATOM_POW && a->exponent.count == 0) piece = rat_atom(atom_ln(a->base, a->id));
        else if (a->kind == ATOM_POW && a->base == BASE_ATOM && atoms[a->id].kind == ATOM_VAR && atoms[a->id].id == 'e')
            piece = (Rat){poly_term((Term){num_int(1), a->exponent}), poly_const(num_int(1))};
        else piece = rat_atom(atom_ln(BASE_ATOM, atom));
        total = rat_add(total, rat_mul(rat_frac(t.mono.factor[i].exp), piece), 0);
    }
    *out = total;
    return !failure;
}

/* Il logaritmo naturale della costante c, che chi chiama sa positiva e
 * senza L. Numeratore e denominatore di un solo termine con term_log();
 * una somma con logarithm() del capitolo 11, che la scompone. Ritorna 0 se
 * non sa scriverlo. */
static int constant_ln(Rat c, Rat *out) {
    Rat side[2];
    for (int s = 0; s < 2; s++) {
        Poly p = s ? c.den : c.num;
        if (p.count == 1) { if (!term_log(p.term[0], &side[s])) return 0; continue; }
        if (!poly_is_real(p)) return 0;
        side[s] = logarithm((Rat){p, poly_const(num_int(1))});
    }
    *out = rat_add(side[0], side[1], 1);
    return !failure;
}

/* e elevato alla costante c, senza L e senza denominatore. Un termine alla
 * volta, perché e^{u + v} = e^u e^v: un razionale r dà e^r, q ln p dà p^q,
 * q M con M un monomio di altre costanti dà (e^M)^q. Ritorna 0 se non sa
 * scriverlo. */
static int constant_exp(Rat c, Rat *out) {
    if (!poly_is_one(c.den)) return 0;
    Rat total = rat_int(1);
    int e = atom_var('e');
    for (int i = 0; i < c.num.count; i++) {
        Term t = c.num.term[i], power = {num_int(1), {0}};
        Frac q = t.coef.re;
        if (t.coef.im.num != 0) return 0;
        const Atom *a = t.mono.count == 1 ? &atoms[t.mono.factor[0].atom] : NULL;
        int one = t.mono.count == 1 && frac_cmp(t.mono.factor[0].exp, frac_int(1)) == 0;
        if (t.mono.count == 0) {
            term_times(&power, e, q);
        } else if (one && a->kind == ATOM_LN && a->base == BASE_PRIME) {
            total = rat_mul(total, q.den == 1 ? rat_pow_int(rat_int(a->id), q.num) : fractional_power(rat_int(a->id), q, 0));
            continue;
        } else if (one && a->kind == ATOM_LN) {
            return 0;
        } else {
            term_times(&power, atom_pow(BASE_ATOM, e, &t.mono), q);
        }
        total = rat_mul(total, (Rat){poly_term(power), poly_const(num_int(1))});
    }
    *out = total;
    return !failure;
}

/* La costante c, positiva, elevata al razionale q non intero. Un termine
 * solo con atomi positivi si eleva fattore per fattore, (r a^k)^q =
 * r^q a^{k q}, che vale per basi positive; anche L lo è. Una somma senza L
 * passa da fractional_power() del capitolo 11. Ritorna 0 se non sa
 * scriverla. */
static int constant_power(Rat c, Frac q, Rat *out) {
    Poly part[2] = {c.num, c.den};
    Rat result[2];

    /* Numeratore e denominatore positivi, cambiando il segno a tutti e due
     * se serve. */
    int side = 1;
    if (part[1].count == 1 && part[1].term[0].mono.count == 0) side = part[1].term[0].coef.re.num > 0 ? 1 : -1;
    else if (constant_sign((Rat){part[1], poly_const(num_int(1))}, &side) != 1) return 0;
    for (int s = 0; s < 2 && side < 0; s++) part[s] = poly_add(poly_const(num_int(0)), part[s], 1);

    for (int s = 0; s < 2; s++) {
        Poly p = part[s];
        if (p.count == 1) {
            Term t = p.term[0], rest = {num_int(1), {0}};
            if (t.coef.im.num != 0 || t.coef.re.num <= 0) return 0;
            for (int i = 0; i < t.mono.count; i++) {
                if (!atom_positive(t.mono.factor[i].atom)) return 0;
                term_times(&rest, t.mono.factor[i].atom, frac_mul(t.mono.factor[i].exp, q));
            }
            result[s] = rat_mul(fractional_power(rat_frac(t.coef.re), q, 0), (Rat){poly_term(rest), poly_const(num_int(1))});
            continue;
        }
        Rat whole = {p, poly_const(num_int(1))};
        if (rat_has_ell(whole) || !poly_is_real(p)) return 0;
        result[s] = fractional_power(whole, q, 0);
    }
    *out = rat_make(poly_mul(result[0].num, result[1].den), poly_mul(result[0].den, result[1].num));
    return !failure;
}

/* Seno e coseno della costante c, senza L e senza denominatore: con le
 * formule di Eulero, come nel capitolo 11. Ritorna 0 se non si può. */
static int constant_sin_cos(Rat c, Rat *sine, Rat *cosine) {
    if (!poly_is_one(c.den) || !poly_is_real(c.num)) return 0;
    Rat forward = exp_i(c, 1), backward = exp_i(c, -1);
    Rat minus_half_i = {poly_const((Num){frac_int(0), (Frac){-1, 2}}), poly_const(num_int(1))};
    *cosine = rat_mul(rat_add(forward, backward, 0), rat_frac((Frac){1, 2}));
    *sine = rat_mul(rat_add(forward, backward, 1), minus_half_i);
    return !failure;
}

/* I VALORI E L'ALGEBRA DEI LIMITI (29g) */

/* L'esponente nullo: nessun fattore e^{G} (29k). */
#define NO_GROWTH ((Series){1, 0, 0, SERIES_FLAT, 1, NULL})

/* I quattro modi di costruire un Value: una serie (positive dice se la
 * funzione è certamente positiva vicino al punto), un limite finito con il
 * lato da cui ci si arriva, un limite infinito con il suo segno, un fallimento
 * (V_UNDEFINED o V_UNKNOWN) con il perché. */
static Value value_series(Series s, int positive) {
    Value v = {V_SERIES, s, 0, {{0, NULL}, {0, NULL}}, 0, positive, NULL, NO_GROWTH};
    return v;
}
static Value value_finite(Rat number, int approach) {
    Value v = {V_LIMIT, {1, 0, 0, 0, 0, NULL}, 0, number, approach, 0, NULL, NO_GROWTH};
    return v;
}
static Value value_infinite(int sign) {
    Value v = {V_LIMIT, {1, 0, 0, 0, 0, NULL}, sign, {{0, NULL}, {0, NULL}}, 0, sign > 0, NULL, NO_GROWTH};
    return v;
}
static Value value_failed(ValueKind kind, const char *why) {
    Value v = {kind, {1, 0, 0, 0, 0, NULL}, 0, {{0, NULL}, {0, NULL}}, 0, 0, why, NO_GROWTH};
    return v;
}

/* IL FATTORE e^{G} (29k) */

/* La funzione piatta: più piccola di ogni potenza di t (29e). */
static Series series_flat(void) { return series_make(1, SERIES_FLAT, 0, SERIES_FLAT, 0); }

/* Ritorna 1 se v ha un fattore e^{G}. */
static int value_grows(Value v) { return v.kind == V_SERIES && v.growth.count > 0; }

/* Dove va l'esponente g (29k-b): ritorna 1 e mette in *dir +1 se tende a
 * +\infty, -1 se tende a -\infty; ritorna 0 se g è zero (test esatto), -1
 * se il segno del suo termine principale non si sa. */
static int growth_direction(Series g, int *dir) {
    Lead lead;
    int found = series_settle(&g, &lead);
    if (found < 0) return 0;
    if (found == 0) return -1;
    *dir = lead.side;
    return 1;
}

/* Ritorna e^{g} s. Un esponente zero (test esatto) si toglie, e così quello
 * di una serie esattamente zero; un esponente che non è più esatto, perché
 * una somma lo ha troncato, non dice più quanto vale il fattore: allora la
 * risposta è "non so". */
static Value value_grown(Series s, Series g, int positive) {
    int dir;
    if (!g.exact) return value_failed(V_UNKNOWN, "un esponente con troppi termini");
    int known = growth_direction(g, &dir);
    if (known == 0 || (s.exact && series_trim(s).count == 0)) return value_series(s, positive);
    if (known < 0) return value_failed(V_UNKNOWN, "un esponenziale di cui non si sa se cresce o decresce");
    Value v = value_series(s, positive);
    v.growth = series_trim(g);
    return v;
}

/* Ritorna v come lo vedeva l'algebra dei limiti prima della scala (29k),
 * per le funzioni che il fattore e^{G} non lo sanno trattare: se G tende a
 * -\infty una funzione piatta, se tende a +\infty l'infinito con il segno
 * del termine principale di S. Un v senza fattore resta com'è. */
static Value value_plain(Value v) {
    if (!value_grows(v)) return v;
    int dir = 0;
    Series s = v.series;
    Lead lead;
    int found = series_settle(&s, &lead);

    /* La direzione di G è nota: value_grown() non costruisce un fattore
     * senza. */
    if (growth_direction(v.growth, &dir) != 1) return value_failed(V_UNKNOWN, "un esponenziale di cui non si sa se cresce o decresce");
    if (dir < 0) return value_series(series_flat(), found == 1 && lead.side > 0);
    if (found == 1) return value_infinite(lead.side);
    if (found < 0 && !s.exact && s.end < SERIES_FLAT) return value_failed(V_UNKNOWN, NEEDS_PRECISION);
    if (found < 0) return value_failed(V_UNKNOWN, "accanto a un esponenziale che cresce resta solo un termine più piccolo di ogni potenza, "
                                                  "di cui non si conosce l'ordine");
    return value_failed(V_UNKNOWN, "un coefficiente dello sviluppo ha un segno che gli intervalli non sanno stabilire");
}

/* Divide la serie s nei termini di esponente negativo, *negative (esatti:
 * chi chiama sa che il resto di s tende a zero), e in tutti gli altri con il
 * resto, *rest (29k-f). */
static void series_split_growth(Series s, Series *negative, Series *rest) {
    int count = s.low < 0 ? -s.low : 0;
    if (count > s.count) count = s.count;
    *negative = series_make(s.den, s.low, count, SERIES_FLAT, 1);
    for (int i = 0; i < negative->count; i++) negative->coef[i] = s.coef[i];
    *negative = series_trim(*negative);
    *rest = s;
    if (s.low < 0) {
        rest->coef += count;
        rest->count -= count;
        rest->low = 0;
        if (rest->count == 0) rest->coef = NULL;
    }
    *rest = series_trim(*rest);
}

/* Il limite della serie s (29c): un V_LIMIT, oppure V_UNKNOWN con il
 * motivo; NEEDS_PRECISION se i coefficienti noti sono tutti zero e il resto
 * non tende a zero. positive dice che la funzione è positiva: allora un
 * limite 0 è 0^{+}. */
static Value series_limit(Series s, int positive) {
    Lead lead;
    int found = series_settle(&s, &lead);
    if (found < 0) {
        if (s.exact || s.end > 0) return value_finite(rat_int(0), positive);
        return value_failed(V_UNKNOWN, NEEDS_PRECISION);
    }
    if (found == 0) return value_failed(V_UNKNOWN, "un coefficiente dello sviluppo ha un segno che gli intervalli non sanno stabilire");
    int top = lead.degree.num > 0, bottom = lead.degree.num < 0;
    if (s.low < 0 || (s.low == 0 && top)) return value_infinite(lead.side);
    if (s.low > 0 || bottom) return value_finite(rat_int(0), lead.side);

    /* Esponente 0 e nessuna potenza di L: il limite è il coefficiente, e
     * da che parte ci si arriva lo dice il termine dopo. */
    Rat number = rat_has_ell(s.coef[0]) ? lead.value : s.coef[0];
    Series rest = s;
    Lead next;
    rest.coef++;
    rest.count--;
    rest.low++;
    int approach = !rat_has_ell(s.coef[0]) && series_settle(&rest, &next) == 1 ? next.side : 0;
    return value_finite(number, approach);
}

/* Ritorna il limite di v: v stesso se non è una serie, altrimenti
 * series_limit(). Con il fattore e^{G} (29k) il limite è 0 se G tende a
 * -\infty, dal lato del segno di S; altrimenti l'infinito di value_plain(). */
static Value value_limit(Value v) {
    if (value_grows(v)) {
        Value plain = value_plain(v);
        if (plain.kind != V_SERIES) return plain;
        Series s = v.series;
        Lead lead;
        return value_finite(rat_int(0), series_settle(&s, &lead) == 1 ? lead.side : 0);
    }
    return v.kind == V_SERIES ? series_limit(v.series, v.positive) : v;
}

/* Il segno del limite finito l, se certo: +1, -1, oppure 0 se il numero è
 * zero; ritorna 0 se non si sa, 1 altrimenti. */
static int limit_sign(Value l, int *side) {
    int known = constant_sign(l.value, side);
    if (known == 0) *side = 0;
    return known >= 0;
}

/* -l, per un limite. */
static Value limit_neg(Value l) {
    if (l.kind != V_LIMIT) return l;
    if (l.infinite) return value_infinite(-l.infinite);
    return value_finite(rat_add(rat_int(0), l.value, 1), -l.approach);
}

/* a + b sui numeri reali estesi. */
static Value limit_add(Value a, Value b) {
    if (a.infinite && b.infinite) return a.infinite == b.infinite ? a : value_failed(V_UNKNOWN, "forma indeterminata: +\\infty - \\infty");
    if (a.infinite) return a;
    if (b.infinite) return b;
    return value_finite(rat_add(a.value, b.value, 0), a.approach == b.approach ? a.approach : 0);
}

/* a b sui numeri reali estesi: 0 per infinito non si scioglie. */
static Value limit_mul(Value a, Value b) {
    int sa = 0, sb = 0;
    if (!a.infinite && !limit_sign(a, &sa)) return value_failed(V_UNKNOWN, "un limite ha un segno che gli intervalli non sanno stabilire");
    if (!b.infinite && !limit_sign(b, &sb)) return value_failed(V_UNKNOWN, "un limite ha un segno che gli intervalli non sanno stabilire");
    if (a.infinite && b.infinite) return value_infinite(a.infinite * b.infinite);
    if (a.infinite || b.infinite) {
        int finite = a.infinite ? sb : sa, sign = a.infinite ? a.infinite : b.infinite;
        return finite ? value_infinite(finite * sign) : value_failed(V_UNKNOWN, "forma indeterminata: 0 \\cdot \\infty");
    }
    int approach = sa == 0 && sb ? a.approach * sb : sb == 0 && sa ? b.approach * sa : 0;
    return value_finite(rat_mul(a.value, b.value), approach);
}

/* 1 / l sui numeri reali estesi: 1/(0^{+}) = +\infty, 1/\infty = 0. Un
 * limite 0 senza segno non si inverte. */
static Value limit_inverse(Value l) {
    int side = 0;
    if (l.infinite) return value_finite(rat_int(0), l.infinite);
    if (!limit_sign(l, &side)) return value_failed(V_UNKNOWN, "un limite ha un segno che gli intervalli non sanno stabilire");
    if (side) return value_finite(rat_div(rat_int(1), l.value), -l.approach);
    if (l.approach) return value_infinite(l.approach);
    return value_failed(V_UNKNOWN, "un divisore tende a 0 senza un segno noto");
}

/* LE SERIE DELLE FUNZIONI (29e) */

/* I coefficienti delle serie di Taylor in 0 che servono, come dati: */
typedef enum {
    TAYLOR_EXP,        /* e^w = somma di w^k / k! */
    TAYLOR_LOG,        /* ln(1 + w) = somma di (-1)^{k+1} w^k / k, da k = 1 */
    TAYLOR_SIN,        /* sin w = somma di (-1)^j w^{2j+1} / (2j+1)! */
    TAYLOR_COS,        /* cos w = somma di (-1)^j w^{2j} / (2j)! */
    TAYLOR_ATAN,       /* arctan w = somma di (-1)^j w^{2j+1} / (2j+1) */
    TAYLOR_BINOMIAL    /* (1 + w)^q = somma di q (q - 1) ... (q - k + 1) / k! w^k */
} TaylorKind;

/* Mette in a[k] il coefficiente di w^k della serie kind (con l'esponente q
 * per TAYLOR_BINOMIAL), per k da 0, e ritorna quanti ne ha messi: al più
 * MAX_TAYLOR, meno se i numeri escono dai razionali. Uscire non è un
 * errore: la serie si tronca prima, e il resto lo dice (series_taylor()). */
static int taylor_coefficients(TaylorKind kind, Frac q, Frac *a) {
    const char *saved = failure;
    Frac factorial = frac_int(1), binomial = frac_int(1);
    int count = 0;
    for (int k = 0; k < MAX_TAYLOR; k++) {
        if (k > 0) {
            factorial = frac_mul(factorial, frac_int(k));
            binomial = frac_div(frac_mul(binomial, frac_add(q, frac_int(1 - k))), frac_int(k));
        }
        Frac sign = frac_int((k / 2) % 2 ? -1 : 1), c = frac_int(0);
        switch (kind) {
        case TAYLOR_EXP: c = frac_div(frac_int(1), factorial); break;
        case TAYLOR_LOG: if (k) c = frac_make(k % 2 ? 1 : -1, k); break;
        case TAYLOR_SIN: if (k % 2) c = frac_div(sign, factorial); break;
        case TAYLOR_COS: if (k % 2 == 0) c = frac_div(sign, factorial); break;
        case TAYLOR_ATAN: if (k % 2) c = frac_make(sign.num, k); break;
        case TAYLOR_BINOMIAL: c = binomial; break;
        }
        if (failure != saved) { failure = saved; break; }
        a[count++] = c;
    }
    return count;
}

/* Ritorna la somma dei a[k] w^k (29b), con w che tende a 0: i suoi
 * esponenti sono positivi. Se w è esatta lo sviluppo si ferma all'esponente
 * target (in unità 1/D di w); altrimenti al resto di w. Il resto della serie
 * troncata a K termini è O(w^K) = O(t^{K v}), con v l'esponente più basso
 * di w, e lo si aggiunge. */
static Series series_taylor(Series w, TaylorKind kind, Frac q, int target) {
    Frac a[MAX_TAYLOR];
    int terms = taylor_coefficients(kind, q, a), ok = 1;

    /* Il risultato ha il denominatore degli esponenti di w: chi chiama lo
     * sposta in quelle unità. Una costante andava riscritta, e senza farlo
     * 1/(2 t^{-5/2}) diventava t^5 / 2 (il controllo con i numeri lo ha
     * visto: tests/limits/false_limits.tex). */
    if (w.exact && w.count == 0) return series_rescale(series_const(rat_frac(a[0])), w.den);
    int v = w.count ? w.low : w.end, end = w.exact ? target : w.end;
    if (v < 1) { fail("uno sviluppo di Taylor con un argomento che non tende a 0"); return series_bounded(); }
    if (end < v) end = v;
    int used = (end + v - 1) / v;
    if (used > terms) used = terms;
    if (used < 1) used = 1;

    /* Horner: a[0] + w (a[1] + w (a[2] + ...)). */
    Series sum = series_rescale(series_const(rat_frac(a[used - 1])), w.den);
    for (int k = used - 2; k >= 0 && ok; k--) {
        sum = series_cut(series_mul(w, sum, &ok), end);
        sum = series_add(sum, series_const(rat_frac(a[k])), 0, &ok);
    }
    if (!ok) fail("denominatori degli esponenti troppo grandi in uno sviluppo");

    /* Il resto della serie troncata; e quello di w, se w non è esatta,
     * anche quando è piatta e il suo resto non ha un esponente. */
    sum = series_cut(sum, used >= SERIES_FLAT / v ? SERIES_FLAT : used * v);
    if (!w.exact) sum.exact = 0;
    return sum;
}

/* Il primo termine di s, che deve essere noto e diverso da zero, tolto da s:
 * s = c t^{low} (1 + u). Mette u in *u e ritorna c. */
static Rat series_unit(Series s, Series *u) {
    Rat c = s.coef[0], inverse = rat_div(rat_int(1), c);
    *u = series_make(s.den, 1, s.count - 1, series_plus(s.end, -s.low), s.exact);
    for (int i = 1; i < s.count && i - 1 < u->count; i++) u->coef[i - 1] = rat_mul(s.coef[i], inverse);
    *u = series_trim(*u);
    return c;
}

/* 1 / s (29c). Ritorna 1 e mette il risultato in *out se il termine
 * principale di s è noto e non nullo; -1 se s è esattamente zero (allora
 * 1/s non ha valori); 0 se non si sa. */
static int series_inverse(Series s, Series *out) {
    Lead lead;
    int found = series_settle(&s, &lead);
    if (found < 0) return s.exact ? -1 : 0;
    if (found == 0) return 0;
    Series u;
    Rat c = series_unit(s, &u);
    Series sum = series_taylor(u, TAYLOR_BINOMIAL, frac_int(-1), lim_goal * s.den + s.low);
    *out = series_shift(series_scale(sum, rat_div(rat_int(1), c)), -s.low);
    return !failure;
}

/* s^n per n intero (29b): moltiplicazioni ripetute, per quadrati. Con n < 0
 * si inverte prima. Ritorna come series_inverse(). */
static int series_power_int(Series s, long long n, Series *out) {
    int ok = 1;
    if (n < 0) {
        int inverted = series_inverse(s, &s);
        if (inverted <= 0) return inverted;
        n = -n;
    }
    Series result = series_const(rat_int(1)), square = s;
    for (; n > 0 && ok; n /= 2) {
        if (n % 2) result = series_mul(result, square, &ok);
        if (n > 1) square = series_mul(square, square, &ok);
    }
    *out = result;
    return ok && !failure;
}

/* s^q per q razionale non intero (29e, 29f): s = c t^{e} (1 + u) dà
 * c^q t^{e q} (1 + u)^q. La base deve essere positiva; con odd diverso da
 * zero (una radice di indice dispari) può essere negativa, e
 * (-b)^q = -(b^q). Ritorna 1 se riesce, -1 se la base è negativa vicino al
 * punto (la potenza non ha valori), 0 se non si sa. */
static int series_power(Series s, Frac q, int odd, Series *out) {
    Lead lead;
    int found = series_settle(&s, &lead);
    if (found < 0 && s.exact) { *out = s; return q.num > 0 ? 1 : -1; }
    if (found <= 0) return 0;
    if (lead.side < 0 && !odd) return -1;
    Series u;
    Rat c = series_unit(s, &u), cq;
    if (lead.side < 0) c = rat_add(rat_int(0), c, 1);
    if (!constant_power(c, q, &cq)) return 0;
    if (lead.side < 0) cq = rat_add(rat_int(0), cq, 1);

    /* L'esponente e q, con il denominatore che serve. */
    Frac shift = frac_make((__int128)s.low * q.num, (__int128)s.den * q.den);
    long long den = lcm_small(s.den, shift.den);
    if (den > MAX_SERIES_DEN || shift.num > MAX_EXPONENT / MAX_SERIES_DEN || shift.num < -MAX_EXPONENT / MAX_SERIES_DEN) return 0;
    Series sum = series_taylor(u, TAYLOR_BINOMIAL, q, lim_goal * s.den);
    sum = series_rescale(sum, (int)den);
    *out = series_shift(series_scale(sum, cq), (int)(shift.num * (den / shift.den)));
    return !failure;
}

/* Divide la serie s in *constant, il coefficiente di t^0 (zero se manca),
 * e *rest, i termini con esponente positivo e il resto. Ritorna 1 se s
 * tende a quel numero, cioè se dopo aver tolto gli zeri iniziali non restano
 * esponenti negativi, il resto tende a zero e il termine costante non
 * contiene L. Il segno del termine costante non serve. */
static int series_split(Series s, Rat *constant, Series *rest) {
    Lead lead;
    series_settle(&s, &lead);
    *constant = rat_int(0);
    if (s.end <= 0 || s.low < 0) return 0;
    *rest = s;
    if (s.count && s.low == 0) {
        *constant = s.coef[0];
        rest->coef++;
        rest->count--;
        rest->low++;
        *rest = series_trim(*rest);
    }
    return !rat_has_ell(*constant);
}

/* Le funzioni sui valori. Ognuna prova la serie (29e) e, se non c'è, il
 * limite (29g); un valore V_UNDEFINED o V_UNKNOWN passa com'è. */

/* e^v. */
static Value value_exp(Value v) {
    if (v.kind == V_UNDEFINED || v.kind == V_UNKNOWN) return v;

    /* Un esponente che ha già un fattore e^{G}: e^{e^{G} S} si sa solo come
     * limite, o come funzione piatta (29k-f). */
    v = value_plain(v);
    if (v.kind == V_UNKNOWN) return v;
    Value l = value_limit(v);
    if (v.kind == V_SERIES) {
        Series s = v.series, rest, negative;
        Rat constant, base;
        Lead lead;

        /* Limitata: e^{O(1)} è O(1), e positiva. Solo se l'O(1) è davvero
         * limitato, cioè se nessun coefficiente contiene L (lim_logs):
         * x \cdot x^{\sin(1/x)} = t e^{-L \sin(1/x)} risultava O(t), e il
         * limite 0 DIMOSTRATO, mentre in x = 1/(3\pi/2 + 2k\pi) la funzione
         * vale 1 (special_cases[] in tests/limits/test_limits.c). */
        if (series_settle(&s, &lead) < 0 && s.end == 0 && !lim_logs) return value_series(series_bounded(), 1);

        /* 29k-f. Se il resto tende a zero i termini di esponente negativo
         * sono noti tutti: sono il fattore e^{N}, e il resto si scrive con
         * il termine costante e una serie di Taylor. Il termine costante può
         * avere L al primo grado con un coefficiente razionale b:
         * e^{a + b L} = e^a t^{-b} (29d). Il coefficiente di t^0 non serve
         * con il segno: anche se gli intervalli non lo sanno dire, e^a si
         * scrive. */
        if (s.end > 0) {
            series_split_growth(s, &negative, &rest);
            s = rest;
            constant = rat_int(0);
            if (s.count && s.low == 0) {
                constant = s.coef[0];
                rest.coef++;
                rest.count--;
                rest.low++;
                rest = series_trim(rest);
            }
            Frac b = frac_int(0);
            int linear = !rat_has_ell(constant);
            if (!linear && poly_is_one(constant.den)) {
                Poly without = poly_const(num_int(0));
                linear = 1;
                for (int i = 0; i < constant.num.count; i++) {
                    Term t = constant.num.term[i];
                    Frac e = mono_exponent(&t.mono, lim_ell);
                    if (e.num == 0) without = poly_add(without, poly_term(t), 0);
                    else if (frac_cmp(e, frac_int(1)) == 0 && t.mono.count == 1 && t.coef.im.num == 0) b = frac_add(b, t.coef.re);
                    else linear = 0;
                }
                constant = (Rat){without, poly_const(num_int(1))};
            }
            long long den = lcm_small(rest.den, b.den);
            if (b.num > MAX_EXPONENT / MAX_SERIES_DEN || b.num < -MAX_EXPONENT / MAX_SERIES_DEN) linear = 0;
            if (linear && den <= MAX_SERIES_DEN && constant_exp(constant, &base)) {
                Series sum = series_scale(series_taylor(rest, TAYLOR_EXP, frac_int(0), lim_goal * rest.den), base);
                sum = series_rescale(sum, (int)den);
                return value_grown(series_shift(sum, (int)(-b.num * (den / b.den))), negative, 1);
            }
        }
    }

    /* Senza uno sviluppo: e^{+\infty} = +\infty, e e^{-\infty} è più
     * piccola di ogni potenza di t, una funzione piatta e positiva. */
    if (l.kind == V_LIMIT && l.infinite > 0) return value_infinite(1);
    if (l.kind == V_LIMIT && l.infinite < 0) return value_series(series_flat(), 1);

    /* e^L per un limite finito L. */
    Rat value;
    if (l.kind == V_LIMIT && !l.infinite && constant_exp(l.value, &value)) {
        Value r = value_finite(value, l.approach);
        r.positive = 1;
        return r;
    }
    return l.kind == V_UNKNOWN ? l : value_failed(V_UNKNOWN, "un esponenziale di cui non si sa scrivere né lo sviluppo né il limite");
}

/* ln v (29d). */
static Value value_ln(Value v) {
    if (v.kind == V_UNDEFINED || v.kind == V_UNKNOWN) return v;

    /* 29k-e. ln(e^{G} S) = G + ln S. */
    if (value_grows(v)) {
        Series s = v.series;
        Lead lead;
        int found = series_settle(&s, &lead), ok = 0;
        if (found == 1 && lead.side < 0) return value_failed(V_UNDEFINED, "il logaritmo di un numero negativo");
        if (found == 1) {
            Value rest = value_ln(value_series(v.series, 1));
            Series sum;
            if (rest.kind == V_SERIES && !value_grows(rest)) sum = series_add(v.growth, rest.series, 0, &ok);
            if (ok && !failure) return value_series(sum, 0);
        }
        v = value_plain(v);
        if (v.kind == V_UNKNOWN) return v;
    }
    if (v.kind == V_SERIES) {
        Series s = v.series, u;
        Lead lead;
        int found = series_settle(&s, &lead);
        if (found == 1 && lead.side < 0) return value_failed(V_UNDEFINED, "il logaritmo di un numero negativo");
        Rat c, logarithm_c;
        if (found == 1 && !rat_has_ell(s.coef[0])) {
            c = series_unit(s, &u);
            if (constant_ln(c, &logarithm_c)) {
                /* ln c - (low/D) L, più ln(1 + u). */
                Rat ell = rat_mul(rat_frac(frac_make(-s.low, s.den)), rat_atom(lim_ell));
                int ok;
                if (s.low) lim_logs = 1;
                Series sum = series_add(series_taylor(u, TAYLOR_LOG, frac_int(0), lim_goal * u.den), series_const(rat_add(logarithm_c, ell, 0)), 0, &ok);
                if (ok) return value_series(sum, 0);
            }
        }
    }
    Value l = value_limit(v);
    if (l.kind != V_LIMIT) return l;
    if (l.infinite) return l.infinite > 0 ? value_infinite(1) : value_failed(V_UNDEFINED, "il logaritmo di un numero negativo");
    int side;
    Rat value;
    if (!limit_sign(l, &side)) return value_failed(V_UNKNOWN, "un limite ha un segno che gli intervalli non sanno stabilire");
    if (side < 0 || (side == 0 && l.approach < 0)) return value_failed(V_UNDEFINED, "il logaritmo di un numero negativo");
    if (side == 0) return l.approach > 0 ? value_infinite(-1) : value_failed(V_UNKNOWN, "l'argomento di un logaritmo tende a 0 senza un segno noto");
    if (!constant_ln(l.value, &value)) return value_failed(V_UNKNOWN, "un logaritmo di una costante che il programma non sa scrivere");
    return value_finite(value, 0);
}

/* sin v, cos v, tan v, cot v: fn dice quale. Seno e coseno di ciò che non
 * tende a un numero sono comunque O(1) (29e). */
static Value value_trig(Value v, Function fn) {
    v = value_plain(v);
    if (v.kind == V_UNDEFINED || v.kind == V_UNKNOWN) return v;
    int quotient = fn == FN_TAN || fn == FN_COT, ok = 1;
    Value bounded = quotient ? value_failed(V_UNKNOWN, "la tangente di qualcosa che non tende a un numero") : value_series(series_bounded(), 0);
    Rat u0, sine, cosine;
    Series s, c, w;
    if (v.kind == V_SERIES) {
        if (!series_split(v.series, &u0, &w)) return bounded;
        if (!constant_sin_cos(u0, &sine, &cosine)) return quotient ? value_failed(V_UNKNOWN, "seno e coseno di una costante") : bounded;
        Series ws = series_taylor(w, TAYLOR_SIN, frac_int(0), lim_goal * w.den), wc = series_taylor(w, TAYLOR_COS, frac_int(0), lim_goal * w.den);
        s = series_add(series_scale(wc, sine), series_scale(ws, cosine), 0, &ok);
        c = series_add(series_scale(wc, cosine), series_scale(ws, sine), 1, &ok);
        if (!ok) return value_failed(V_UNKNOWN, "denominatori degli esponenti troppo grandi");
        if (fn == FN_SIN) return value_series(s, 0);
        if (fn == FN_COS) return value_series(c, 0);
        Series inverse, result;
        int inverted = series_inverse(fn == FN_TAN ? c : s, &inverse);
        if (inverted < 0) return value_failed(V_UNDEFINED, "una tangente dove il coseno vale zero");
        if (inverted > 0) result = series_mul(fn == FN_TAN ? s : c, inverse, &ok);
        if (inverted > 0 && ok) return value_series(result, 0);
        return value_failed(V_UNKNOWN, "il denominatore di una tangente ha uno sviluppo di cui non si trova il termine principale");
    }
    if (v.infinite) return bounded;
    if (!constant_sin_cos(v.value, &sine, &cosine)) return value_failed(V_UNKNOWN, "seno e coseno di una costante");
    if (fn == FN_SIN) return value_finite(sine, 0);
    if (fn == FN_COS) return value_finite(cosine, 0);
    int side;
    Rat below = fn == FN_TAN ? cosine : sine;
    if (constant_sign(below, &side) != 1) return value_failed(V_UNKNOWN, "una tangente in un punto in cui non si sa se il coseno è zero");
    return value_finite(rat_div(fn == FN_TAN ? sine : cosine, below), 0);
}

/* arctan v (29e). */
static Value value_arctan(Value v) {
    v = value_plain(v);
    if (v.kind == V_UNDEFINED || v.kind == V_UNKNOWN) return v;
    Rat half_pi = rat_div(rat_atom(atom_var(VAR_PI)), rat_int(2)), u0;
    int ok = 1;
    if (v.kind == V_SERIES) {
        Series s = v.series, w, inverse;
        Lead lead;
        int found = series_settle(&s, &lead);

        /* Verso +\infty o -\infty: \pm pi/2 - arctan(1/v). */
        if (found == 1 && s.low < 0 && series_inverse(s, &inverse) == 1) {
            Series sum = series_taylor(inverse, TAYLOR_ATAN, frac_int(0), lim_goal * inverse.den);
            sum = series_add(series_const(lead.side > 0 ? half_pi : rat_add(rat_int(0), half_pi, 1)), sum, 1, &ok);
            if (ok) return value_series(sum, 0);
        }

        /* Verso un numero u0: arctan u0 + arctan(w / (1 + u0 v)). È la
         * formula di sottrazione, arctan a - arctan b = arctan((a - b) /
         * (1 + a b)), che vale quando a b > -1: qui a b = u0 v tende a
         * u0^2, e 1 + u0 v resta lontano da zero. */
        if (series_split(s, &u0, &w) && poly_is_real(u0.num) && poly_is_real(u0.den)) {
            Series below = series_add(series_const(rat_int(1)), series_scale(s, u0), 0, &ok), z;
            if (ok && series_inverse(below, &z) == 1) {
                z = series_mul(w, z, &ok);
                Series sum = series_add(series_const(arctangent(u0)), series_taylor(z, TAYLOR_ATAN, frac_int(0), lim_goal * z.den), 0, &ok);
                if (ok && !failure) return value_series(sum, 0);
            }
        }
        return value_series(series_bounded(), 0);
    }
    Value l = value_limit(v);
    if (l.kind != V_LIMIT) return value_series(series_bounded(), 0);
    if (l.infinite) return value_finite(l.infinite > 0 ? half_pi : rat_add(rat_int(0), half_pi, 1), -l.infinite);
    if (!poly_is_real(l.value.num) || !poly_is_real(l.value.den)) return value_series(series_bounded(), 0);
    return value_finite(arctangent(l.value), 0);
}

/* v^n, per n intero. */
static Value value_power_int(Value v, long long n) {
    if (v.kind == V_UNDEFINED || v.kind == V_UNKNOWN) return v;
    if (n == 0) return value_series(series_const(rat_int(1)), 1);
    if (n > MAX_POWER || n < -MAX_POWER) return value_failed(V_UNKNOWN, "un esponente intero troppo grande");
    Series result;
    if (v.kind == V_SERIES) {
        /* 29k-e: (e^{G} S)^n = e^{n G} S^n. */
        int done = series_power_int(v.series, n, &result);
        if (done < 0) return value_failed(V_UNDEFINED, "una potenza negativa di una funzione che vale zero");
        if (done > 0) return value_grown(result, series_scale(v.growth, rat_int(n)), v.positive);
        v = value_plain(v);
        if (v.kind == V_UNKNOWN) return v;
    }
    Value l = value_limit(v), r = value_finite(rat_int(1), 0);
    if (l.kind != V_LIMIT) return l;
    if (n < 0) { l = limit_inverse(l); n = -n; }
    for (long long i = 0; i < n && r.kind == V_LIMIT; i++) r = limit_mul(r, l);
    return r;
}

/* v^q per q razionale non intero; odd come per series_power(). */
static Value value_power(Value v, Frac q, int odd) {
    if (v.kind == V_UNDEFINED || v.kind == V_UNKNOWN) return v;
    const char *negative = odd ? "" : "una potenza a esponente non intero, o una radice di indice pari, di un numero negativo";
    Series result;
    if (v.kind == V_SERIES) {
        /* 29k-e: (e^{G} S)^q = e^{q G} S^q, perché e^{G} > 0; con una
         * radice di indice dispari e S < 0, -(e^{q G} |S|^q). */
        int done = series_power(v.series, q, odd, &result);
        if (done < 0) return value_failed(V_UNDEFINED, q.num < 0 && v.series.exact ? "una potenza negativa di zero" : negative);
        if (done > 0) return value_grown(result, series_scale(v.growth, rat_frac(q)), 0);
        v = value_plain(v);
        if (v.kind == V_UNKNOWN) return v;
    }
    Value l = value_limit(v);
    int side;
    Rat value;
    if (l.kind != V_LIMIT) return l;
    if (l.infinite) {
        if (l.infinite < 0 && !odd) return value_failed(V_UNDEFINED, negative);
        return q.num > 0 ? value_infinite(l.infinite) : value_finite(rat_int(0), l.infinite);
    }
    if (!limit_sign(l, &side)) return value_failed(V_UNKNOWN, "un limite ha un segno che gli intervalli non sanno stabilire");
    if ((side < 0 || (side == 0 && l.approach < 0)) && !odd) return value_failed(V_UNDEFINED, negative);
    if (side == 0 && !l.approach) return value_failed(V_UNKNOWN, "la base di una potenza tende a 0 senza un segno noto");
    if (side == 0) return q.num > 0 ? value_finite(rat_int(0), l.approach) : value_infinite(l.approach);
    Rat base = side < 0 ? rat_add(rat_int(0), l.value, 1) : l.value;
    if (!constant_power(base, q, &value)) return value_failed(V_UNKNOWN, "una potenza di una costante che il programma non sa scrivere");
    return value_finite(side < 0 ? rat_add(rat_int(0), value, 1) : value, 0);
}

/* |v|. */
static Value value_abs(Value v) {
    if (v.kind == V_UNDEFINED || v.kind == V_UNKNOWN) return v;
    if (v.kind == V_SERIES) {
        /* |e^{G} S| = e^{G} |S|. */
        Series s = v.series;
        Lead lead;
        int found = series_settle(&s, &lead);
        if (found == 1) return value_grown(lead.side < 0 ? series_scale(s, rat_int(-1)) : s, v.growth, 1);
        if (found < 0) return value_grown(s, v.growth, 0);
        v = value_plain(v);
        if (v.kind == V_UNKNOWN) return v;
    }
    Value l = value_limit(v);
    int side;
    if (l.kind != V_LIMIT) return l;
    if (l.infinite) return value_infinite(1);
    if (!limit_sign(l, &side)) return value_failed(V_UNKNOWN, "un limite ha un segno che gli intervalli non sanno stabilire");
    return value_finite(side < 0 ? rat_add(rat_int(0), l.value, 1) : l.value, side ? 0 : l.approach ? 1 : 0);
}

/* 29k-c, 29k-d. a + b, a - b, a b, a / b con un fattore e^{G} in almeno
 * uno dei due, tutti e due serie. Ritorna V_UNKNOWN se il conto non si fa:
 * allora chi chiama ricomincia con value_plain(). */
static Value growth_binary(NodeKind op, Value a, Value b, int positive) {
    int ok = 1, dir;
    if (op == N_MUL || op == N_DIV) {
        Series factor = b.series;
        if (op == N_DIV) {
            int inverted = series_inverse(b.series, &factor);
            if (inverted < 0) return value_failed(V_UNDEFINED, "una divisione per una funzione che vale zero");
            if (inverted == 0) return value_failed(V_UNKNOWN, "un divisore con un esponenziale di cui non si trova il termine principale");
        }
        Series s = series_mul(a.series, factor, &ok), g = ok ? series_add(a.growth, b.growth, op == N_DIV, &ok) : NO_GROWTH;
        if (!ok || failure) return value_failed(V_UNKNOWN, "denominatori degli esponenti troppo grandi");
        return value_grown(s, g, positive);
    }

    /* Una somma con uno zero esatto è l'altro addendo, esatto com'è: lo zero
     * non ha esponente, ma non per questo "cresce di più" di e^{-1/t}. Per
     * l'invariante di Value uno zero esatto non ha fattore. */
    if (a.series.exact && series_trim(a.series).count == 0) return op == N_SUB ? value_grown(series_scale(b.series, rat_int(-1)), b.growth, 0) : b;
    if (b.series.exact && series_trim(b.series).count == 0) return a;

    /* Una somma: chi cresce di più, con la differenza degli esponenti. */
    Series delta = series_add(a.growth, b.growth, 1, &ok);
    int known = ok && delta.exact ? growth_direction(delta, &dir) : -1;
    if (known < 0) return value_failed(V_UNKNOWN, "non si sa quale dei due esponenziali cresce di più");
    if (known == 0) {
        Series s = series_add(a.series, b.series, op == N_SUB, &ok);
        return ok ? value_grown(s, a.growth, positive) : value_failed(V_UNKNOWN, "denominatori degli esponenti troppo grandi");
    }

    /* Quello che cresce di meno diventa una funzione piatta accanto
     * all'altro (29k-c). */
    Value big = dir > 0 ? a : b;
    Series s = dir < 0 && op == N_SUB ? series_scale(big.series, rat_int(-1)) : big.series;
    s = series_add(s, series_flat(), 0, &ok);
    return ok ? value_grown(s, big.growth, positive) : value_failed(V_UNKNOWN, "denominatori degli esponenti troppo grandi");
}

/* a + b, a - b, a b, a / b: op è N_ADD, N_SUB, N_MUL o N_DIV. */
static Value value_binary(NodeKind op, Value a, Value b) {
    if (a.kind == V_UNDEFINED) return a;
    if (b.kind == V_UNDEFINED) return b;
    if (a.kind == V_UNKNOWN) return a;
    if (b.kind == V_UNKNOWN) return b;
    int ok = 0, positive = a.positive && b.positive && op != N_SUB;
    Series result, inverse;

    /* Con il fattore e^{G} (29k); se il conto non si fa, l'algebra dei
     * limiti come prima della scala. */
    if (value_grows(a) || value_grows(b)) {
        if (a.kind == V_SERIES && b.kind == V_SERIES) {
            Value r = growth_binary(op, a, b, positive);
            if (r.kind != V_UNKNOWN) return r;
            failure = NULL;
        }
        a = value_plain(a);
        b = value_plain(b);
        if (a.kind == V_UNKNOWN) return a;
        if (b.kind == V_UNKNOWN) return b;
    }
    if (a.kind == V_SERIES && b.kind == V_SERIES) {
        if (op == N_ADD || op == N_SUB) result = series_add(a.series, b.series, op == N_SUB, &ok);
        if (op == N_MUL) result = series_mul(a.series, b.series, &ok);
        if (op == N_DIV) {
            int inverted = series_inverse(b.series, &inverse);
            if (inverted < 0) return value_failed(V_UNDEFINED, "una divisione per una funzione che vale zero");
            if (inverted > 0) result = series_mul(a.series, inverse, &ok);
        }
        if (ok && !failure) return value_series(result, positive);
    }
    Value la = value_limit(a), lb = value_limit(b), r;
    if (la.kind != V_LIMIT) return la;
    if (lb.kind != V_LIMIT) return lb;
    if (op == N_ADD) r = limit_add(la, lb);
    else if (op == N_SUB) r = limit_add(la, limit_neg(lb));
    else if (op == N_MUL) r = limit_mul(la, lb);
    else if (la.infinite && lb.infinite) r = value_failed(V_UNKNOWN, "forma indeterminata: \\infty / \\infty");
    else if (!la.infinite && !lb.infinite && la.value.num.count == 0 && lb.value.num.count == 0) r = value_failed(V_UNKNOWN, "forma indeterminata: 0 / 0");
    else r = (lb = limit_inverse(lb)).kind == V_LIMIT ? limit_mul(la, lb) : lb;
    if (r.kind == V_LIMIT) r.positive = positive;
    return r;
}

/* Se v è una costante esatta (una serie esatta con il solo termine t^0, o
 * zero) la mette in *c e ritorna 1. */
static int value_constant(Value v, Rat *c) {
    if (v.kind != V_SERIES || value_grows(v) || !v.series.exact || v.series.count > 1 || (v.series.count == 1 && v.series.low != 0)) return 0;
    *c = v.series.count ? v.series.coef[0] : rat_int(0);
    return 1;
}

/* Se il conto r non è riuscito e uno dei suoi operandi a, b è una serie di
 * cui non si conosce nessun coefficiente, ritorna NEEDS_PRECISION: con più
 * termini il termine principale di quell'operando può comparire (29c).
 * Altrimenti ritorna r. */
static Value precision_or(Value r, Value a, Value b) {
    Value operand[2] = {a, b};
    if (r.kind != V_UNKNOWN) return r;
    for (int i = 0; i < 2; i++) {
        Series s = operand[i].series;
        Lead lead;
        if (operand[i].kind == V_SERIES && series_settle(&s, &lead) < 0 && !s.exact && s.end < SERIES_FLAT)
            return value_failed(V_UNKNOWN, NEEDS_PRECISION);
    }
    return r;
}

/* Prototipo in avanti inevitabile: una funzione ha argomenti, che sono
 * espressioni, e il logaritmo e la radice hanno anche una base e un indice. */
static Value limit_eval(const Node *node);

/* Ritorna arcsin u, o arccos u se cosine è 1, scritto con l'arcotangente e
 * la radice quadrata, le funzioni che lo sviluppo in serie conosce:
 *
 *     \arcsin u = 2 \arctan(u / (1 + \sqrt{1 - u^2})),     \arccos u = \pi/2 - \arcsin u.
 *
 * È la bisezione dell'angolo: se a = \arcsin u, con a tra -\pi/2 e \pi/2,
 * allora tan(a/2) = sin a / (1 + cos a) = u / (1 + \sqrt{1 - u^2}), perché
 * cos a = \sqrt{1 - u^2} non è negativo; e a/2 sta tra -\pi/4 e \pi/4, dove
 * l'arcotangente inverte la tangente. Vale anche in u = 1 e u = -1, e non
 * altrove, perché fuori da [-1, 1] la radice non c'è: il campo di esistenza
 * è lo stesso. L'albero ritornato sta nell'arena e condivide u. */
static Node *arcsin_by_arctan(Node *u, int cosine) {
    Node *root = node_call(FN_ROOT, node_new(N_SUB, node_num(1), node_new(N_POW, u, node_num(2))), node_num(2));
    Node *value = node_new(N_MUL, node_num(2), node_call(FN_ARCTAN, node_new(N_DIV, u, node_new(N_ADD, node_num(1), root)), NULL));
    if (!cosine) return value;
    Node *pi = node_new(N_VAR, NULL, NULL);
    pi->name = VAR_PI;
    return node_new(N_SUB, node_new(N_DIV, pi, node_num(2)), value);
}

/* Il valore della chiamata di funzione node, con l'argomento che vale a. */
static Value limit_call(const Node *node, Value a) {
    Rat c;
    Num index;
    switch ((Function)node->op) {
    case FN_SIN: case FN_COS: case FN_TAN: case FN_COT:
        return value_trig(a, (Function)node->op);
    case FN_ARCTAN:
        return value_arctan(a);
    case FN_ARCSIN: case FN_ARCCOS:
        /* L'argomento si ricalcola dentro la riscrittura: a non serve. */
        return limit_eval(arcsin_by_arctan(node->a, node->op == FN_ARCCOS));
    case FN_LN:
        return value_ln(a);
    case FN_LOG:
        return value_binary(N_DIV, value_ln(a), value_ln(limit_eval(node->b)));
    case FN_ABS:
        return value_abs(a);
    case FN_ROOT:
        if (!value_constant(limit_eval(node->b), &c) || !rat_number(c, &index) || index.im.num != 0 || index.re.den != 1 || index.re.num < 2)
            return value_failed(V_UNKNOWN, "una radice con un indice che non è un intero da 2 in su");
        return value_power(a, (Frac){1, index.re.num}, index.re.num % 2);
    default:
        return value_failed(V_UNKNOWN, "una funzione che il capitolo dei limiti non tratta");
    }
}

/* Il valore dell'espressione node vicino al punto, dal lato in corso. Le
 * lettere ammesse sono la variabile, e e pi (lo controlla prove_limit()). */
static Value limit_eval(const Node *node) {
    Value a, b;
    Rat c;
    Num number;
    if (failure) return value_failed(V_UNKNOWN, failure);
    switch (node->kind) {
    case N_NUM:
        return value_series(series_const(rat_int(node->value)), node->value > 0);
    case N_VAR:
        if (node->name == VAR_PI || node->name == 'e') return value_series(series_const(rat_atom(atom_var(node->name))), 1);
        if (node->name != lim_x) return value_failed(V_UNKNOWN, "una lettera diversa dalla variabile del limite");
        if (lim_moved) {
            /* 29l: x = \pm e^{1/t} all'infinito, x = \pm e^{-1/t} vicino a 0. */
            Series g = series_make(1, -1, 1, SERIES_FLAT, 1);
            int sign = lim_infinity ? lim_infinity : lim_side;
            if (!g.count) return value_failed(V_UNKNOWN, OUT_OF_MEMORY);
            g.coef[0] = rat_int(lim_infinity ? 1 : -1);
            return value_grown(series_const(rat_int(sign)), g, sign > 0);
        }
        if (lim_infinity) {
            /* x = 1/t oppure x = -1/t. */
            Series s = series_make(1, -1, 1, SERIES_FLAT, 1);
            if (!s.count) return value_failed(V_UNKNOWN, OUT_OF_MEMORY);
            s.coef[0] = rat_int(lim_infinity);
            return value_series(s, lim_infinity > 0);
        } else {
            /* x = a + t oppure x = a - t. */
            Series s = series_make(1, 0, 2, SERIES_FLAT, 1);
            if (!s.count) return value_failed(V_UNKNOWN, OUT_OF_MEMORY);
            s.coef[0] = lim_point;
            s.coef[1] = rat_int(lim_side);
            return value_series(series_trim(s), 0);
        }
    case N_NEG:
        a = limit_eval(node->a);
        return precision_or(value_binary(N_SUB, value_series(series_const(rat_int(0)), 0), a), a, a);
    case N_ADD: case N_SUB: case N_MUL: case N_DIV:
        a = limit_eval(node->a);
        b = limit_eval(node->b);
        return precision_or(value_binary(node->kind, a, b), a, b);
    case N_POW:
        b = limit_eval(node->b);
        a = limit_eval(node->a);
        if (b.kind == V_UNDEFINED || b.kind == V_UNKNOWN) return b;

        /* Un esponente costante razionale: una potenza (29f). */
        if (value_constant(b, &c) && rat_number(c, &number) && number.im.num == 0)
            return precision_or(number.re.den == 1 ? value_power_int(a, number.re.num) : value_power(a, number.re, 0), a, a);

        /* f^g = e^{g ln f}, definita dove f > 0. La dimostrazione lo dice
         * quando conta, cioè quando la base dipende dalla variabile. */
        lim_exponential |= node_has_variable(node->b, lim_x) && node_has_variable(node->a, lim_x);
        return precision_or(value_exp(value_binary(N_MUL, b, value_ln(a))), a, b);
    case N_CALL:
        a = limit_eval(node->a);
        return precision_or(limit_call(node, a), a, a);
    default:
        return value_failed(V_UNKNOWN, "somme, prodotti e successioni con l'indice non sono trattati nei limiti");
    }
}

/* UN LATO ALLA VOLTA (29a) */

/* Gli esiti del controllo con i numeri di un lato (29i). */
typedef enum { CHECK_UNCONFIRMED, CHECK_CONFIRMED, CHECK_CONTRADICTED } CheckResult;

/* Il limite da un lato: ciò che il conto ha dato e ciò che i numeri ne
 * dicono. */
typedef struct {
    int side;          /* +1 da destra, -1 da sinistra, 0 per un punto all'infinito */
    Value value;       /* la funzione vicino al punto */
    Value limit;       /* il suo limite: V_LIMIT, V_UNDEFINED o V_UNKNOWN */
    int quotient;      /* 1 se la funzione è un quoziente: allora parts[] sono i suoi termini */
    Value parts[2];
    CheckResult check; /* il controllo con i numeri */
    int first, last;   /* i k dei punti x = a \pm 2^{-k} o x = \pm 2^{k} che il controllo ha usato */
    int moved;         /* 1 se il conto è fatto con la sostituzione di 29l */
    int goal;          /* la precisione del conto ritornato, lim_goal: l'ordine del certificato (29n) */
} SideResult;

/* Calcola in *r il limite di f dal lato side (29a), con precisioni via via
 * più alte finché il termine principale non si trova (29c). Se così non si
 * arriva a un limite, e il punto è 0 o un infinito, si riprova salendo di un
 * piano (29l): r->moved lo dice, e lim_moved resta quello del conto
 * ritornato. La memoria dell'ultimo tentativo resta: la usa la
 * dimostrazione scritta. */
static void limit_side(const Node *f, int side, SideResult *r) {
    int goals = (int)(sizeof series_goals / sizeof *series_goals);
    int moves = lim_infinity || lim_point.num.count == 0 ? 2 : 1;
    const char *first = NULL;
    memset(r, 0, sizeof *r);
    r->side = side;
    for (int moved = 0; moved < moves; moved++) {
        /* Se anche il secondo piano non arriva a un limite, il motivo da
         * dire è quello del primo, il conto dei libri. */
        if (moved) first = r->limit.why;
        for (int g = 0; g < goals; g++) {
            Scratch mark = scratch_mark();
            failure = NULL;
            lim_goal = r->goal = series_goals[g];
            lim_side = side;
            lim_moved = r->moved = moved;
            lim_logs = 0;
            lim_ell = atom_var(VAR_LOG_SCALE);
            r->quotient = f->kind == N_DIV;
            if (r->quotient) {
                r->parts[0] = limit_eval(f->a);
                r->parts[1] = limit_eval(f->b);
                r->value = precision_or(value_binary(N_DIV, r->parts[0], r->parts[1]), r->parts[0], r->parts[1]);
            } else {
                r->value = limit_eval(f);
            }
            r->limit = value_limit(r->value);
            if (failure) r->limit = value_failed(V_UNKNOWN, failure);
            failure = NULL;
            if (r->limit.kind != V_UNKNOWN) return;
            if (r->limit.why != NEEDS_PRECISION || g + 1 == goals) {
                if (moved + 1 == moves) {
                    if (first) r->limit.why = first;
                    return;
                }
                scratch_drop(mark);
                break;
            }
            scratch_drop(mark);
        }
    }
}

/* Ritorna l'intervallo di x nel punto k-esimo del lato di r: a \pm 2^{-k},
 * oppure \pm 2^{k} all'infinito. */
static Range sample_point(const SideResult *r, int k, Range point) {
    double t = 1;
    for (int i = 0; i < k; i++) t /= 2;
    if (lim_infinity) return (Range){lim_infinity / t, lim_infinity / t};
    return range_add(point, (Range){r->side * t, r->side * t});
}

/* Ritorna l'intervallo di L = ln(1/t) nel punto k-esimo: k ln 2, perché
 * t = 2^{-k}; con la sostituzione di 29l ln(k ln 2), perché lì
 * 1/t = |ln |x - a|| = k ln 2. */
static Range ell_at(const SideResult *r, int k) {
    Range ell = range_mul(range_ratio(k, 1), range_ln2());
    return r->moved ? range_ln(ell) : ell;
}

/* Ritorna l'intervallo di c t^e L^d, con t^e = e^{-e L}. */
static Range leading_at(Range c, Frac e, Frac d, Range ell) {
    Range power = range_exp(range_mul(range_ratio(-e.num, e.den), ell));
    Range logs = d.den == 1 ? range_power(ell, d.num) : range_exp(range_mul(range_ratio(d.num, d.den), range_ln(ell)));
    return range_mul(c, range_mul(power, logs));
}

/* Ritorna l'intervallo del fattore e^{G} (29k) dove L vale ell: G è esatto,
 * e si calcola termine per termine, con L nei coefficienti. */
static Range growth_at(Series g, Range ell) {
    Range sum = {0, 0};
    lim_ell_range = ell;
    for (int i = 0; i < g.count; i++) {
        if (g.coef[i].num.count == 0) continue;
        Range power = range_exp(range_mul(range_ratio(-(g.low + i), g.den), ell));
        sum = range_add(sum, range_mul(constant_range(g.coef[i]), power));
    }
    lim_ell_range = range_none();
    return range_exp(sum);
}

/* Ritorna un intervallo per ln|g(far)| - ln|g(near)|, con g = c t^e L^d
 * e^{G} e L che vale near e far nei due punti: -e (far - near) +
 * d (ln far - ln near) + G(far) - G(near), senza calcolare g, che uscirebbe
 * dai numeri della macchina. Il coefficiente c si cancella. */
static Range leading_climb(Frac e, Frac d, Series g, Range near, Range far) {
    Range climb = range_add(range_mul(range_ratio(-e.num, e.den), range_sub(far, near)),
                            range_mul(range_ratio(d.num, d.den), range_sub(range_ln(far), range_ln(near))));
    for (int i = 0; i < g.count; i++) {
        if (g.coef[i].num.count == 0) continue;
        Range rate = range_ratio(-(g.low + i), g.den), at[2];
        for (int k = 0; k < 2; k++) {
            lim_ell_range = k ? far : near;
            at[k] = range_mul(constant_range(g.coef[i]), range_exp(range_mul(rate, lim_ell_range)));
        }
        lim_ell_range = range_none();
        climb = range_add(climb, range_sub(at[1], at[0]));
    }
    return climb;
}

/* La stima del resto del controllo con i numeri, 16 (1 + |L|) t^{B} con
 * t^{B} = e^{-B ell}, come numero sicuramente non più grande del vero; -1
 * se non si calcola. number contiene il limite L. */
static double remainder_limit(Range number, Frac bound, Range ell) {
    Range power = range_exp(range_mul(range_ratio(-bound.num, bound.den), ell));
    return range_known(power) ? 16 * (1 + (number.high > -number.low ? number.high : -number.low)) * power.low : -1;
}

/* 29i. Il controllo con i numeri del lato r: la funzione f calcolata con gli
 * intervalli (node_range(), capitolo 24) nei punti t = 2^{-k}, contro ciò che
 * il conto ha dato. Vedi la testa del capitolo per il criterio e per ciò che
 * garantisce. Mette l'esito in r->check, e in r->first, r->last i k usati. */
static void limit_check(const Node *f, SideResult *r) {
    Range point = lim_infinity ? range_none() : constant_range(lim_point), number = range_none(), c = range_none();
    Frac e = {0, 1}, d = {0, 1};
    Series growth = NO_GROWTH;
    int expected = 0, finite = r->limit.kind == V_LIMIT && !r->limit.infinite, defined[2] = {0, 0}, count = 0;
    r->check = CHECK_UNCONFIRMED;
    if (!lim_infinity && !range_known(point)) return;

    /* Il termine principale atteso, di f - L o di f, se il conto l'ha dato
     * con una serie. Con il fattore e^{G} il limite finito è 0, e f - 0 è
     * e^{G} S: il termine principale è quello di S, per e^{G}. */
    /* Senza termine principale, ma con un resto noto per f - L, il resto dà
     * una stima: |f - L| <= C t^{E} se f - L = O(t^{E}), e |f - L| è più
     * piccolo di ogni potenza se è piatta o ha un fattore e^{G} con
     * G -> -\infty. Il controllo chiede allora |f - L| <= 16 (1 + |L|) t^{B}
     * nell'ultimo punto, con B = min(E, 1), e B = 4 per una funzione piatta:
     * un L sbagliato lascia |f - L| vicino a un numero fisso, e non passa
     * (vedi la testa del capitolo). B = 4 perché a volte i soli punti che
     * si sanno calcolare hanno t ancora grande, come e^{1/x^2} che esce dai
     * numeri della macchina già in x = 1/32, o dopo la sostituzione di 29l,
     * dove t = 1/(k ln 2). */
    int bounded = 0;
    Frac bound = {4, 1};
    if (finite) number = constant_range(r->limit.value);
    if (r->limit.kind == V_LIMIT && r->value.kind == V_SERIES) {
        int ok = 1, grows = value_grows(r->value);
        Series s = finite && !grows ? series_add(r->value.series, series_const(r->limit.value), 1, &ok) : r->value.series;
        Lead lead;
        int found = ok ? series_settle(&s, &lead) : 0;
        if (found == 1) {
            expected = 1;
            c = constant_range(lead.value);
            e = frac_make(s.low, s.den);
            d = lead.degree;
            if (grows) growth = r->value.growth;
        } else if (found < 0 && finite && !s.exact && s.end > 0) {
            bounded = 1;
            if (!grows && s.end < SERIES_FLAT) bound = s.end < s.den ? frac_make(s.end, s.den) : frac_int(1);
        }
        failure = NULL;
    }

    /* I punti, finché stanno dalla parte giusta del punto. Dopo la
     * sostituzione di 29l L cresce come ln k: i punti vanno più lontano. Con
     * un fattore e^{G} la funzione esce presto dai numeri della macchina
     * ((1 + e^{1/x^3})^{\sin x} già in x = 1/16): si parte allora da k = 1,
     * e conta l'ultimo punto che si sa calcolare. */
    Range kept[2] = {range_none(), range_none()};
    int kept_count = 0, step = r->moved ? 4 : 1, top = r->moved ? MOVED_SAMPLES : LIMIT_SAMPLES;
    for (int k = growth.count ? 1 : 4; k <= top; k += step) {
        Range x = sample_point(r, k, point);
        if (!range_known(x) || (!lim_infinity && (r->side > 0 ? x.low <= point.high : x.high >= point.low))) break;
        int nowhere = 0;
        Range value = node_range(f, lim_x, x, &nowhere);
        defined[count % 2] = nowhere ? -1 : range_known(value) ? 1 : 0;  /* gli ultimi due punti */
        count++;
        if (nowhere || !range_known(value) || r->limit.kind != V_LIMIT) continue;

        /* Il rapporto con il termine principale, oppure f - L, oppure f. Un
         * punto serve se l'intervallo è abbastanza stretto da dire qualcosa:
         * la larghezza decide solo quali punti guardare, non che cosa è
         * vero, che lo dicono poi i confronti certi tra intervalli. */
        Range q;
        double width;
        if (expected) {
            Range ell = ell_at(r, k);
            q = range_div(finite ? range_sub(value, number) : value, range_mul(leading_at(c, e, d, ell), growth_at(growth, ell)));
            width = 0.5;
        } else if (finite) {
            q = range_sub(value, number);
            width = (1 + (number.high > -number.low ? number.high : -number.low)) / 8;

            /* Con la stima del resto, un punto serve se l'intervallo è
             * stretto rispetto alla stima in quel punto. */
            double tight = bounded ? remainder_limit(number, bound, ell_at(r, k)) / 4 : -1;
            if (tight >= 0 && tight < width) width = tight;
        } else {
            q = range_mul(value, range_ratio(r->limit.infinite, 1));
            width = (q.low + q.high) / 2;
            width = (width < 0 ? -width : width) / 2;
        }
        if (!range_known(q) || q.high - q.low > width) continue;
        if (!r->first) r->first = k;
        r->last = k;
        kept[0] = kept[1];
        kept[1] = q;
        kept_count++;
    }

    /* Il campo di esistenza: negli ultimi due punti la funzione deve non
     * avere valori se il conto dice così, e averne altrimenti. */
    int last_two = count >= 2;
    if (r->limit.kind == V_UNDEFINED) {
        if (last_two && defined[0] < 0 && defined[1] < 0) r->check = CHECK_CONFIRMED;
        if (last_two && defined[0] > 0 && defined[1] > 0) r->check = CHECK_CONTRADICTED;
        return;
    }
    if (last_two && defined[0] < 0 && defined[1] < 0) { r->check = CHECK_CONTRADICTED; return; }
    if (r->limit.kind != V_LIMIT || kept_count == 0) return;

    /* Il valore. Con il termine principale g, anche la sua direzione: g
     * deve scendere tra due punti lontani se il limite è finito (f - L ~ g
     * va a zero), salire se è infinito. Così la regola che dal termine
     * principale ricava il limite (29c, 29k) è ricontrollata anche lei con i
     * numeri: un segno sbagliato di G la fa uscire, anche se f ~ g. */
    Range last = kept[1], before = kept[0];
    if (expected) {
        int out_last = last.high < 1.0 / 16 || last.low > 16, out_before = kept_count >= 2 && (before.high < 1.0 / 16 || before.low > 16);
        /* I due punti lontani, come valori di L = ln(1/t): è la formula di g
         * che si guarda, non f, e L può essere grande quanto si vuole. Con
         * un fattore e^{G} non troppo, perché G(t) resti tra i numeri della
         * macchina (G vi domina comunque il resto); senza, lontanissimi,
         * perché t^{e} batta L^{d} anche con d grande, come in
         * (\ln x)^{100} / x. */
        int side;
        Range near = growth.count ? range_mul(range_ratio(64, 1), range_ln2()) : range_ratio(1000000, 1);
        Range far = growth.count ? range_mul(range_ratio(256, 1), range_ln2()) : range_ratio(1000000000000, 1);
        Range climb = leading_climb(e, d, growth, near, far);

        /* Con un esponenziale, nel termine principale o in un termine
         * piatto accanto, i soli punti che si sanno calcolare possono stare
         * dove il termine principale non domina ancora: e^{\sqrt{1/t}}
         * supera t^{-7} solo da t = 2^{-12}, ma e^{2/t} esce dai numeri
         * della macchina già da t = 2^{-9}, e e^{-3/t} da t = 2^{-8}, anche
         * se trascurabile. Lì un rapporto lontano da 1 non conferma, ma non
         * smentisce: smentisce solo con un fattore e^{G} assente e punti
         * fino a t = 2^{-20}, come il limite infinito più sotto. */
        if (out_last && out_before) r->check = growth.count || r->last < 20 ? CHECK_UNCONFIRMED : CHECK_CONTRADICTED;
        else if (range_side(climb, &side) && side != (finite ? -1 : 1)) r->check = CHECK_CONTRADICTED;
        else if (last.low >= 1.0 / 16 && last.high <= 16) r->check = CHECK_CONFIRMED;
    } else if (finite && bounded) {
        double limit = remainder_limit(number, bound, ell_at(r, r->last));
        if (limit >= 0 && last.low >= -limit && last.high <= limit) r->check = CHECK_CONFIRMED;
    } else if (finite) {
        double size = (1 + (number.high > -number.low ? number.high : -number.low)) / 2;
        if (last.low >= -size && last.high <= size) r->check = CHECK_CONFIRMED;
    } else {
        if (kept_count >= 2 && r->last >= 20 && last.high < 0 && before.high < 0) r->check = CHECK_CONTRADICTED;
        else if (last.low >= 1) r->check = CHECK_CONFIRMED;
    }
}

/* LA DIMOSTRAZIONE SCRITTA */

/* Scrive il polinomio p, che contiene la lettera L, come somma di potenze
 * di L con i loro coefficienti tra parentesi. */
static void put_ell_poly(Poly p) {
    int written = 0;
    while (p.count > 0) {
        Frac top = mono_exponent(&p.term[0].mono, lim_ell);
        for (int i = 1; i < p.count; i++)
            if (frac_cmp(mono_exponent(&p.term[i].mono, lim_ell), top) > 0) top = mono_exponent(&p.term[i].mono, lim_ell);
        Term *high = terms_alloc(p.count), *low = terms_alloc(p.count);
        if (!high || !low) { unwritable = 1; return; }
        int highs = 0, lows = 0;
        for (int i = 0; i < p.count; i++) {
            Term t = p.term[i];
            if (frac_cmp(mono_exponent(&t.mono, lim_ell), top) != 0) { low[lows++] = t; continue; }
            t.mono = mono_with_exponent(&t.mono, lim_ell, frac_int(0));
            high[highs++] = t;
        }
        /* Un coefficiente razionale si scrive com'è, 1 e -1 davanti a L
         * si tacciono; gli altri vanno tra parentesi. */
        Poly group = poly_finish(high, p.count, highs);
        Num number;
        if (rat_number((Rat){group, poly_const(num_int(1))}, &number) && number.im.num == 0) {
            Frac size = number.re.num < 0 ? frac_neg(number.re) : number.re;
            proof_add("%s", number.re.num < 0 ? (written ? " - " : "-") : (written ? " + " : ""));
            if (size.num != 1 || size.den != 1 || !top.num) put_frac(size);
        } else {
            proof_add("%s\\left(", written ? " + " : "");
            put_terms(group);
            proof_add("\\right)");
        }
        written++;
        if (top.num) { proof_add(" L"); if (top.num != 1 || top.den != 1) { proof_add("^{"); put_frac(top); proof_add("}"); } }
        p = poly_finish(low, p.count, lows);
    }
}

/* Scrive il coefficiente c, anche con la lettera L. */
static void put_coefficient(Rat c) {
    if (!rat_has_ell(c)) { put_rat(c); return; }
    if (poly_is_one(c.den)) { put_ell_poly(c.num); return; }
    proof_add("\\frac{");
    put_ell_poly(c.num);
    proof_add("}{");
    put_ell_poly(c.den);
    proof_add("}");
}

/* Scrive t^{e}: niente per e = 0, t per e = 1. */
static void put_t_power(Frac e) {
    if (e.num == 0) return;
    proof_add("t");
    if (e.num != 1 || e.den != 1) { proof_add("^{"); put_frac(e); proof_add("}"); }
}

/* Scrive la serie s, al più shown termini con un coefficiente scritto
 * diverso da zero, e il resto. Ritorna 0, senza scrivere nulla, se un
 * coefficiente non si sa scrivere (contiene seni e coseni di costanti).
 *
 * Il resto scritto deve contenere tutto ciò che non si scrive. Se restano
 * termini non nulli oltre i primi shown, il resto parte dal primo di loro:
 * per t -> 0^+ i termini seguenti, con esponenti più alti, e il resto
 * calcolato O(t^{end}) sono tutti O(t^{e}), con e l'esponente del primo
 * omesso. Scrivere O(t^{end}) dopo aver tolto dei termini sarebbe falso: era
 * l'errore per cui 1/(1 + t) diventava "1 - t + O(t^{4})", dove manca
 * t^{2} - t^{3}. Una serie esatta (una somma finita) scrive invece i
 * puntini, che non dicono nulla di falso. */
static int put_series(Series s, int shown) {
    size_t start = proof_length;
    int written = 0, omitted = -1;
    unwritable = 0;
    s = series_trim(s);
    for (int i = 0; i < s.count; i++) {
        Rat c = s.coef[i];
        Num number;
        Frac e = frac_make(s.low + i, s.den);
        if (c.num.count == 0) continue;
        if (written == shown) { omitted = i; break; }
        if (rat_number(c, &number) && number.im.num == 0) {
            Frac size = number.re.num < 0 ? frac_neg(number.re) : number.re;
            int unit = size.num == 1 && size.den == 1 && e.num != 0;
            proof_add("%s", number.re.num < 0 ? (written ? " - " : "-") : (written ? " + " : ""));
            if (!unit) put_frac(size);
            if (!unit && e.num) proof_add("\\,");
        } else {
            if (written) proof_add(" + ");
            proof_add("\\left(");
            put_coefficient(c);
            proof_add("\\right)");
            if (e.num) proof_add("\\,");
        }
        put_t_power(e);
        written++;
    }
    /* Il resto: dal primo termine omesso, se c'è (vedi sopra). */
    if (s.exact && omitted >= 0) proof_add(" + \\dots");
    if (!s.exact && omitted < 0 && s.end >= SERIES_FLAT) proof_add("%so\\left(t^{k}\\right) \\text{ for every } k", written ? " + " : "");
    else if (!s.exact) {
        Frac e = frac_make(omitted >= 0 ? s.low + omitted : s.end, s.den);
        proof_add("%sO\\left(", written ? " + " : "");
        if (e.num == 0) proof_add("1"); else put_t_power(e);
        proof_add("\\right)");
    }
    if (s.exact && !written) proof_add("0");
    if (!unwritable && !failure) return 1;
    proof_cut(start);
    unwritable = 0;
    failure = NULL;
    return 0;
}

/* Scrive il limite l (V_LIMIT): +\infty, -\infty o il numero, e ne ritorna
 * il pezzo in *span. Ritorna 0, senza scrivere nulla, se il numero non si sa
 * scrivere. */
static int put_limit(Value l, Span *span) {
    span->from = proof_length;
    if (l.infinite) proof_add(l.infinite > 0 ? "+\\infty" : "-\\infty");
    else if (!put_value("", l.value, span)) return 0;
    span->to = proof_length;
    return 1;
}

/* Ritorna 1 se le lettere di node sono solo x (se non è 0), e e pi, e non
 * ci sono somme, successioni o applicazioni. */
static int limit_letters(const Node *node, int x) {
    if (!node) return 1;
    if (node->kind == N_VAR) return node->name == x || node->name == 'e' || node->name == VAR_PI;
    if (node->kind == N_SEQ || node->kind == N_BIGOP || node->kind == N_APPLY) return 0;
    return limit_letters(node->a, x) && limit_letters(node->b, x) && limit_letters(node->c, x);
}

/* Ritorna 1 se il testo text, un valore scritto (+\infty, -\infty o
 * un'espressione senza la variabile), riletto con il lettore del capitolo 9
 * e calcolato da capo, è il limite l (29j). */
static int limit_reread(const char *text, Value l) {
    int infinite = infinity_text(text, text + strlen(text));
    if (infinite) return infinite == l.infinite;
    if (l.infinite) return 0;
    Node *tree = parse_expression(text);
    Rat value;
    int side;
    if (syntax_error || !limit_letters(tree, 0) || !value_constant(limit_eval(tree), &value) || failure) {
        syntax_error = NULL;
        failure = NULL;
        return 0;
    }
    return constant_sign(rat_add(value, l.value, 1), &side) == 0;
}

/* Copia il pezzo span della dimostrazione in text, lungo al più size. */
static void span_copy(Span span, char *text, size_t size) {
    snprintf(text, size, "%.*s", (int)(span.to - span.from), proof_text + span.from);
}

/* Scrive la funzione v, una serie con il suo eventuale fattore e^{G}
 * (29k), al più shown termini della serie; ritorna 0, senza scrivere
 * nulla, come put_series(). L'esponente G è esatto e si scrive per intero. */
static int put_value_series(Value v, int shown) {
    size_t start = proof_length;
    if (!value_grows(v)) return put_series(v.series, shown);
    proof_add("e^{");
    int ok = put_series(v.growth, MAX_SERIES_TERMS);
    proof_add("} \\left(");
    ok = ok && put_series(v.series, shown);
    proof_add("\\right)");
    if (!ok) proof_cut(start);
    return ok;
}

/* Scrive il pezzo della dimostrazione che riguarda il lato r dell'enunciato
 * st, e ritorna 1 se il valore scritto, riletto, è quello calcolato. */
static int put_side_proof(const LimitStatement *st, const SideResult *r) {
    static const char *const names[] = {"From the left", "At $+\\infty$", "From the right"};
    const char *name = lim_infinity ? (lim_infinity > 0 ? "At $+\\infty$" : "At $-\\infty$") : names[r->side + 1];
    proof_add("\\item \\emph{%s}, with $x = ", name);
    if (r->moved) proof_add("%se^{%s\\frac{1}{t}}", (lim_infinity ? lim_infinity : r->side) < 0 ? "-" : "", lim_infinity ? "" : "-");
    else if (lim_infinity) proof_add(lim_infinity > 0 ? "\\frac{1}{t}" : "-\\frac{1}{t}");
    else if (st->point->kind == N_NUM && st->point->value == 0) proof_add(r->side > 0 ? "t" : "-t");
    else { put_node(st->point, 1); proof_add(r->side > 0 ? " + t" : " - t"); }
    proof_add("$ and $t \\to 0^{+}$%s: ", r->moved ? " (an increasing change of variable, which keeps the limit: the substitution with "
                                                     "$x$ a power of $t$ does not reach a limit here)" : "");
    if (r->limit.kind == V_UNDEFINED) {
        proof_add("the function has no value for any small $t$ (%s).\n", r->limit.why);
        return 1;
    }
    if (r->quotient && r->parts[0].kind == V_SERIES && r->parts[1].kind == V_SERIES) {
        size_t start = proof_length;
        proof_add("the numerator is $");
        int ok = put_value_series(r->parts[0], 3);
        proof_add("$ and the denominator is $");
        ok = ok && put_value_series(r->parts[1], 3);
        proof_add("$, so the function is $");
        ok = ok && put_value_series(r->value, 2);
        proof_add("$");
        if (!ok) { proof_cut(start); proof_add("the expansions of numerator and denominator have coefficients that are not written here"); }
    } else if (r->value.kind == V_SERIES) {
        size_t start = proof_length;
        proof_add("the function is $");
        if (put_value_series(r->value, 3)) proof_add("$");
        else { proof_cut(start); proof_add("the expansion of the function has coefficients that are not written here"); }
    } else {
        proof_add("the function has no expansion in powers of $t$, and the rules of the algebra of limits give its limit");
    }
    Span span;
    proof_add("; so the limit is $");
    if (!put_limit(r->limit, &span)) { proof_cut(proof_length - 1); proof_add("a number that is not written here.\n"); return 1; }
    proof_add("$.\n");
    char text[MAX_FORMULA];
    span_copy(span, text, sizeof text);
    return limit_reread(text, r->limit);
}

/* Scrive la riga del controllo con i numeri (29i) per il lato r. */
static void put_check(const SideResult *r) {
    const char *where = lim_infinity ? "" : r->side > 0 ? " on the right" : " on the left";
    if (r->limit.kind == V_UNDEFINED)
        proof_add("The function has no value%s at the points $t = 2^{-k}$ closest to $0$. ", where);
    else if (r->limit.kind == V_LIMIT && r->moved)
        proof_add("%s the values%s at $x = %s2^{%sk}$ for $k = %d, %d, \\dots, %d$, computed with interval arithmetic, agree with the result. ",
                  r->side < 0 ? "And" : "Directly from the function,", where, (lim_infinity ? lim_infinity : r->side) < 0 ? "-" : "",
                  lim_infinity ? "" : "-", r->first, r->first + 4, r->last);
    else if (r->limit.kind == V_LIMIT)
        proof_add("%s the values%s at $t = 2^{-k}$ for $k = %d, \\dots, %d$, computed with interval arithmetic, agree with the result. ",
                  r->side < 0 ? "And" : "Directly from the function,", where, r->first, r->last);
}

/* Ritorna 1 se i due limiti a e b (V_LIMIT) sono uguali, 0 se sono
 * certamente diversi, -1 se non si sa. */
static int limits_equal(Value a, Value b) {
    int side;
    if (a.infinite || b.infinite) return a.infinite == b.infinite;
    int known = constant_sign(rat_add(a.value, b.value, 1), &side);
    return known < 0 ? -1 : known == 0;
}

/* Il principio di ogni conto su un limite scritto in formula: ripartenza da
 * zero (l'arena, la tabella degli atomi; il testo della dimostrazione no,
 * perché limit_leading() non scrive e non deve cancellare), la lettura in
 * *st, le lettere ammesse, il punto in lim_point e il valore
 * dell'enunciato, se c'è, in *claimed. Ritorna NULL se riesce, altrimenti
 * il perché. */
static const char *limit_start(const char *formula, LimitStatement *st, Rat *claimed) {
    arena_used = arena_keep;
    atom_count = base_poly_count = atan_count = 0;
    failure = NULL;
    env_count = 0;
    conditions_on = 0;
    lim_exponential = lim_moved = lim_logs = 0;
    lim_point = *claimed = rat_int(0);
    if (!parse_limit_statement(formula, st)) return syntax_error;
    if (st->variable == 'e' || !limit_letters(st->function, st->variable) || !limit_letters(st->point, 0) || !limit_letters(st->value, 0))
        return "in un limite le lettere ammesse sono la variabile, e (il numero di Nepero) e \\pi";
    lim_x = st->variable;
    lim_infinity = st->infinity;
    lim_ell = atom_var(VAR_LOG_SCALE);
    lim_goal = series_goals[0];

    /* Il punto e il valore dell'enunciato: due costanti. */
    if ((st->point && !value_constant(limit_eval(st->point), &lim_point)) || (st->value && !value_constant(limit_eval(st->value), claimed)) || failure) {
        failure = NULL;
        return "il punto, o il valore dell'enunciato, non è un numero che il programma sa calcolare";
    }
    return NULL;
}

/* 29n. IL CERTIFICATO
 *
 * Il conto di ogni lato diventa un certificato per checker.c (il suo
 * capitolo 14), che rifà gli sviluppi da sé, con la sua aritmetica: la
 * funzione, il punto, ciò che si afferma con la sua verità, e per ogni lato
 * la sostituzione (29a, o 29l se il conto è salito di un piano) con la
 * precisione lim_goal a cui il conto è riuscito. Del conto del motore il
 * verificatore non riceve nient'altro: ricalcola il termine principale, e da
 * quello il limite.
 *
 * Che cosa si afferma: per DIMOSTRATO l'enunciato, vero; per FALSO
 * l'enunciato, falso; per RISOLTO la risposta riletta dal testo scritto
 * (29j), vera. Per una successione il certificato parla della funzione con
 * n reale: se questa ha limite la successione ha lo stesso (teorema ponte).
 * Un "non esiste" a +\infty non è mai vero per il verificatore, perché lì
 * c'è un lato solo: e nemmeno per il motore, che lo dichiara falso.
 *
 * Le risposte, come per la tabella dei segni (18p-15). Accettato: il
 * verdetto porta il certificato. Respinto: il motore e il verificatore non
 * sono d'accordo, quindi nel dubbio non è dimostrato, e il passo conta tra
 * quelli che non hanno superato il controllo. Non controllabile, o una
 * funzione che la notazione non sa dire (l'arcocotangente): il verdetto resta
 * e dice perché il certificato manca.
 *
 * La funzione si scrive con limit_cert_node(), non con cert_node() del
 * capitolo 13: qui la lettera e è il numero di Nepero, non un parametro, e
 * le funzioni elementari hanno le loro parole. */

/* Scrive l'albero n nella notazione dei limiti di checker.c (i suoi capitoli
 * 6 e 14), con x la variabile: (exp 1) per e, (exp u) per e^{u}, (pi), le
 * funzioni con le loro parole, \log_{b} a come (/ (ln a) (ln b)), come lo
 * calcola limit_call(). Ciò che la notazione non ha rende certificate_broken
 * uguale a 1.
 *
 * Warning: se limit_call() impara una funzione nuova, aggiungila qui e nel
 * capitolo 14 di checker.c. */
static void limit_cert_node(const Node *n, int x) {
    static const char *const binary[] = {[N_ADD] = "+", [N_SUB] = "-", [N_MUL] = "*", [N_DIV] = "/", [N_POW] = "^"};
    static const struct { Function fn; const char *word; } calls[] = {
        {FN_SIN, "sin"}, {FN_COS, "cos"}, {FN_TAN, "tan"}, {FN_COT, "cot"}, {FN_ARCTAN, "atan"},
        {FN_ARCSIN, "arcsin"}, {FN_ARCCOS, "arccos"}, {FN_LN, "ln"}, {FN_ABS, "abs"},
    };
    switch (n->kind) {
    case N_NUM:
        cert_add("%lld", n->value);
        return;
    case N_VAR:
        if (n->name == x) cert_letter(x);
        else if (n->name == 'e') cert_add("(exp 1)");
        else if (n->name == VAR_PI) cert_add("(pi)");
        else certificate_broken = 1;
        return;
    case N_NEG:
        cert_add("(neg ");
        limit_cert_node(n->a, x);
        cert_add(")");
        return;
    case N_ADD: case N_SUB: case N_MUL: case N_DIV: case N_POW:
        if (n->kind == N_POW && n->a->kind == N_VAR && n->a->name == 'e') {
            cert_add("(exp ");
            limit_cert_node(n->b, x);
            cert_add(")");
            return;
        }
        cert_add("(%s ", binary[n->kind]);
        limit_cert_node(n->a, x);
        cert_add(" ");
        limit_cert_node(n->b, x);
        cert_add(")");
        return;
    case N_CALL:
        if (n->op == FN_LOG && n->b) {
            cert_add("(/ (ln ");
            limit_cert_node(n->a, x);
            cert_add(") (ln ");
            limit_cert_node(n->b, x);
            cert_add("))");
            return;
        }
        if (n->op == FN_ROOT) {
            /* (root m a): l'indice prima, come nel capitolo 6 di checker.c. */
            cert_add("(root ");
            limit_cert_node(n->b, x);
            cert_add(" ");
            limit_cert_node(n->a, x);
            cert_add(")");
            return;
        }
        for (size_t i = 0; i < sizeof calls / sizeof *calls; i++)
            if (calls[i].fn == (Function)n->op) {
                cert_add("(%s ", calls[i].word);
                limit_cert_node(n->a, x);
                cert_add(")");
                return;
            }
        certificate_broken = 1;
        return;
    default:
        certificate_broken = 1;
    }
}

/* Scrive in certificate_text il certificato del limite st, calcolato nei
 * lati sides[0..count-1], che afferma claim (con il valore value se è
 * LIMIT_VALUE) con la verità truth. */
static void limit_certificate(const LimitStatement *st, const SideResult *sides, int count, LimitClaim claim, const Node *value, int truth) {
    static const char *const claims[] = {[LIMIT_ASKED] = "", [LIMIT_VALUE] = "value", [LIMIT_PLUS] = "plus", [LIMIT_MINUS] = "minus",
                                         [LIMIT_UNSIGNED] = "unsigned", [LIMIT_NONE] = "none"};
    certificate_length = 0;
    certificate_broken = claim == LIMIT_ASKED;
    cert_add("certificate limit\nvariable ");
    cert_letter(st->variable);
    cert_add("\npoint ");
    if (st->infinity) {
        cert_add(st->infinity > 0 ? "+infinity" : "-infinity");
    } else {
        limit_cert_node(st->point, st->variable);
        if (st->side) cert_add(st->side > 0 ? " right" : " left");
    }
    cert_add("\nfunction ");
    limit_cert_node(st->function, st->variable);
    cert_add("\nclaim %s ", claims[claim]);
    if (claim == LIMIT_VALUE) {
        limit_cert_node(value, st->variable);
        cert_add(" ");
    }
    cert_add(truth ? "true" : "false");

    /* I lati, nell'ordine di prove_limit(): da destra, poi da sinistra. */
    for (int i = 0; i < count; i++) {
        const SideResult *r = &sides[i];
        int toward = st->infinity ? st->infinity : r->side;
        const char *substitution = st->infinity ? (r->moved ? (toward > 0 ? "e^(1/t)" : "-e^(1/t)") : (toward > 0 ? "1/t" : "-1/t"))
                                                : (r->moved ? (toward > 0 ? "e^(-1/t)" : "-e^(-1/t)") : (toward > 0 ? "a+t" : "a-t"));
        cert_add("\nside %s %s %d", st->infinity ? "infinity" : toward > 0 ? "right" : "left", substitution, r->goal);
    }
    cert_add("\nend\n");
}

/* 29n. Fa controllare a checker.c il verdetto *verdict sul limite st, con i
 * lati sides[0..count-1], e lo aggiorna con la risposta (vedi "Le risposte"
 * in testa a 29n). claim, value e truth sono ciò che il certificato
 * afferma. */
static void limit_certify(const LimitStatement *st, const SideResult *sides, int count, LimitClaim claim, const Node *value, int truth, Verdict *verdict) {
    static char problem[512];
    const char *why = "la funzione usa qualcosa che la notazione dei certificati non ha", *text = certificate_text;
    limit_certificate(st, sides, count, claim, value, truth);
    if (!certificate_broken) {
        CkAnswer answer = ck_check(&text, &why, checker_steps());
        if (answer == CK_ACCEPTED) {
            verdict->certificate = certificate_text;
            verdict->reason = NULL;
            return;
        }
        if (answer == CK_REJECTED) {
            unjustified_steps++;
            snprintf(problem, sizeof problem, "il verificatore indipendente ha respinto il certificato del limite: %s", why);
            *verdict = (Verdict){NOT_PROVED, 0, 0, 0, problem, NULL, NULL, NULL, NULL, NULL};
            return;
        }
        snprintf(problem, sizeof problem, "il verificatore non sa controllarlo, %s", why);
    } else {
        snprintf(problem, sizeof problem, "%s", why);
    }

    /* Il motivo sta nella riga del verdetto, e per una richiesta prima del
     * ": " dopo il quale viene la risposta (vedi sign_certify()). */
    for (char *colon = problem; (colon = strchr(colon, ':')) != NULL;) *colon = ',';
    verdict->reason = problem;
}

/* 29j. Prova a dimostrare, smentire o risolvere l'enunciato sul limite
 * scritto in formula (vedi la testa del capitolo). Svuota l'arena e la
 * tabella degli atomi: i risultati di chiamate precedenti non sono più
 * validi. */
Verdict prove_limit(const char *formula) {
    static char answer[MAX_FORMULA];
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    LimitStatement st;
    SideResult sides[2];
    Rat claimed;
    proof_reset();
    if ((verdict.reason = limit_start(formula, &st, &claimed))) return verdict;

    /* I lati, e per ognuno il controllo con i numeri. */
    int count = st.infinity || st.side ? 1 : 2;
    for (int i = 0; i < count; i++) {
        limit_side(st.function, count == 1 ? (st.infinity ? 0 : st.side) : 1 - 2 * i, &sides[i]);
        limit_check(st.function, &sides[i]);
    }

    /* Ogni lato deve essere calcolato e confermato dai numeri. */
    verdict.outcome = NOT_PROVED;
    for (int i = 0; i < count; i++) {
        if (sides[i].limit.kind == V_UNKNOWN) { verdict.reason = sides[i].limit.why; return verdict; }
        if (sides[i].check == CHECK_CONTRADICTED) {
            unjustified_steps++;
            verdict.reason = "il controllo con i numeri contraddice il limite calcolato";
            return verdict;
        }
        if (sides[i].check != CHECK_CONFIRMED) { verdict.reason = "il controllo con i numeri non conferma il limite calcolato"; return verdict; }
    }

    /* Il limite: da un lato solo, o dai due. Un lato senza valori non conta
     * (29a); se nessuno ne ha, il punto non è di accumulazione. */
    int undefined = (sides[0].limit.kind == V_UNDEFINED) + (count == 2 && sides[1].limit.kind == V_UNDEFINED);
    if (undefined == count) {
        verdict.reason = "vicino al punto la funzione non ha valori: il limite non ha senso";
        return verdict;
    }
    int exists = 1;
    Value l = sides[0].limit.kind == V_LIMIT ? sides[0].limit : sides[1].limit;
    if (count == 2 && !undefined) {
        int same = limits_equal(sides[0].limit, sides[1].limit);
        if (same < 0) { verdict.reason = "non si sa se i limiti da destra e da sinistra sono uguali"; return verdict; }
        exists = same;
    }

    /* La dimostrazione: un lato alla volta, poi il controllo, poi la
     * conclusione. Ogni valore scritto viene riletto. */
    int sound = 1, logs = 0, grows = 0;
    for (int i = 0; i < count; i++) {
        const Value *shown[3] = {&sides[i].value, &sides[i].parts[0], &sides[i].parts[1]};
        for (int j = 0; j < 3; j++) {
            if (shown[j]->kind != V_SERIES) continue;
            for (int k = 0; k < shown[j]->series.count; k++) logs |= rat_has_ell(shown[j]->series.coef[k]);
            for (int k = 0; k < shown[j]->growth.count; k++) logs |= rat_has_ell(shown[j]->growth.coef[k]);
            grows |= value_grows(*shown[j]);
        }
    }
    proof_add("\\textbf{Proof.} ");
    if (lim_exponential) proof_add("A power $f^{g}$ with the variable in the exponent means $e^{g \\ln f}$, defined where $f > 0$. ");
    if (grows)
        proof_add("A factor $e^{G}$, with $G$ a finite sum of negative powers of $t$, is larger or smaller than every power of $t$ and of "
                  "$\\ln\\frac{1}{t}$, according to the sign of the leading term of $G$ (the scale of growth: exponentials beat powers, "
                  "which beat logarithms); in a sum the smaller factor becomes a remainder smaller than every power of $t$. ");
    proof_add("Each one-sided limit is computed with expansions in powers of a variable $t \\to 0^{+}$, with exact coefficients "
              "(Taylor's theorem with Peano's remainder)%s; the limit is given by the leading term.\n\\begin{itemize}\n",
              logs ? ", where $L = \\ln\\frac{1}{t}$" : "");
    for (int i = 0; i < count; i++) sound = put_side_proof(&st, &sides[i]) && sound;
    proof_add("\\item \\emph{Check with numbers.} ");
    for (int i = 0; i < count; i++) put_check(&sides[i]);
    proof_add("\n\\end{itemize}\n");
    if (count == 2 && undefined) proof_add("Only one side of the point is in the domain, so the limit is the one from that side. ");
    else if (count == 2 && exists) proof_add("The two one-sided limits are equal, so they are the limit. ");
    else if (count == 2) proof_add("The two one-sided limits are different, so the limit does not exist. ");

    /* Il verdetto, confrontando il limite con ciò che l'enunciato dice. */
    int side = 0, holds = 0;
    switch (st.claim) {
    case LIMIT_ASKED: holds = 1; break;
    case LIMIT_NONE: holds = !exists; break;
    case LIMIT_PLUS: holds = exists && l.infinite > 0; break;
    case LIMIT_MINUS: holds = exists && l.infinite < 0; break;
    case LIMIT_UNSIGNED: holds = exists ? l.infinite != 0 : sides[0].limit.infinite && sides[1].limit.infinite; break;
    case LIMIT_VALUE:
        if (!exists || l.infinite) break;
        int known = constant_sign(rat_add(l.value, claimed, 1), &side);
        if (known < 0) { verdict.reason = "non si sa se il limite calcolato è il valore dell'enunciato"; return verdict; }
        holds = known == 0;
        break;
    }
    /* Ciò che il certificato afferma (29n): l'enunciato, oppure la risposta
     * riletta. */
    LimitStatement reread = st;
    int truth = holds;
    if (st.claim == LIMIT_ASKED) {
        /* La risposta: l'enunciato con il valore, scritto e riletto. Deve
         * rileggersi come un enunciato sul limite, e il valore come quello
         * calcolato. */
        const char *from = st.from, *to = st.to;
        char value[MAX_FORMULA];
        while (to > from && isspace((unsigned char)to[-1])) to--;
        if (!exists) {
            snprintf(answer, sizeof answer, "\\nexists %.*s", (int)(to - from), from);
            verdict.note = "i limiti da destra e da sinistra sono diversi";
        } else {
            Span span;
            proof_add("The limit is $");
            if (!put_limit(l, &span)) { verdict.reason = "il limite è un numero che il programma non sa scrivere"; return verdict; }
            proof_add("$. ");
            span_copy(span, value, sizeof value);
            snprintf(answer, sizeof answer, "%.*s = %s", (int)(to - from), from, value);
        }
        int read = parse_limit_statement(answer, &reread);
        syntax_error = NULL;
        sound = sound && read && (exists ? reread.claim != LIMIT_NONE && reread.claim != LIMIT_ASKED && limit_reread(value, l) : reread.claim == LIMIT_NONE);
        verdict.outcome = SOLVED;
        verdict.method = "con le serie troncate";
        verdict.detail = answer;
    } else if (holds) {
        proof_add("This is what the statement says.");
        verdict.outcome = PROVED;
        verdict.method = "con le serie troncate";
    } else {
        proof_add("The statement says otherwise, so it is false.");
        verdict.outcome = REFUTED;
        verdict.note = exists ? "il limite calcolato è un altro" : "il limite non esiste: i limiti da destra e da sinistra sono diversi";
    }
    proof_add(" $\\Box$");
    if (!sound) {
        unjustified_steps++;
        verdict.outcome = NOT_PROVED;
        verdict.reason = "un valore scritto nella dimostrazione, riletto dal testo, non è quello calcolato";
        return verdict;
    }
    verdict.proof = proof_text;
    if (st.claim == LIMIT_ASKED) truth = 1;
    limit_certify(&st, sides, count, reread.claim, reread.value, truth, &verdict);
    return verdict;
}

/* 29m. IL TERMINE PRINCIPALE, PER CHI LO CHIEDE
 *
 * Il confronto degli integrali impropri (30l) vuole sapere come una funzione
 * va a zero, o all'infinito, vicino a un estremo: il suo termine principale
 * c t^{e} L^{d} e^{G}, cioè f = c t^{e} L^{d} e^{G} (1 + o(1)). È lo stesso
 * conto di un limite (29b-29h, 29k), con lo stesso controllo con i numeri
 * (29i), che deve confermarlo; del coefficiente c servono solo il segno e
 * che non sia zero, che il conto decide in modo esatto (29c). */

/* Il termine principale della funzione della richiesta formula,
 * "\lim_{x \to a^{\pm}} f" o "\lim_{x \to \pm\infty} f", se il controllo con
 * i numeri conferma il conto. Non lo dà se il conto è riuscito solo salendo
 * di un piano (29l): lì t non è più |x - a| o 1/|x|. Svuota l'arena e la
 * tabella degli atomi come prove_limit(). */
LeadingTerm limit_leading(const char *formula) {
    LeadingTerm out = {0, 0, 0, {0, 1}, {0, 1}, 0};
    LimitStatement st;
    SideResult r;
    Rat claimed;
    Lead lead;
    if (limit_start(formula, &st, &claimed) || st.claim != LIMIT_ASKED || (!st.infinity && !st.side)) return out;
    limit_side(st.function, st.infinity ? 0 : st.side, &r);
    limit_check(st.function, &r);
    if (r.check == CHECK_CONTRADICTED) unjustified_steps++;
    Series s = r.value.series;
    int dir = 0, found = r.value.kind == V_SERIES ? series_settle(&s, &lead) : 0;
    failure = NULL;
    if (r.check != CHECK_CONFIRMED || r.limit.kind != V_LIMIT || r.moved || r.value.kind != V_SERIES || found == 0) return out;
    if (value_grows(r.value) && growth_direction(r.value.growth, &dir) != 1) return out;

    /* Nessun coefficiente noto: una funzione piatta, o zero, è più piccola
     * di ogni potenza, come con G -> -\infty; altrimenti resta il resto. */
    if (found < 0) {
        if (dir > 0) return out;
        if (dir < 0 || s.exact || s.end >= SERIES_FLAT) return (LeadingTerm){1, 0, 0, {0, 1}, {0, 1}, -1};
        return (LeadingTerm){1, 1, 0, frac_make(s.end, s.den), {0, 1}, 0};
    }
    return (LeadingTerm){1, 0, lead.side, frac_make(s.low, s.den), lead.degree, dir};
}
