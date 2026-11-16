/* =============================================================================
 * mathresearcher: dimostratore di enunciati matematici scritti in LaTeX
 * =============================================================================
 *
 * COSA FA
 *
 * Legge enunciati nella variabile intera n, scritti in LaTeX, per esempio
 *
 *     \sum_{k=1}^{n} k 2^{k} = \left(n - 1\right) 2^{n + 1} + 2
 *
 * e prova a dimostrarli per induzione su n. Per ogni enunciato risponde:
 *
 *   - DIMOSTRATO: caso base e passo induttivo sono stati verificati;
 *   - FALSO: esiste un n, che viene stampato, in cui i due membri differiscono;
 *   - NON DIMOSTRATO: il metodo si applica ma non chiude la dimostrazione;
 *   - NON SUPPORTATO: l'enunciato usa notazioni o conti fuori dalla portata.
 *
 * Allo stesso modo dimostra le disuguaglianze in n, come 2^n >= n^3 da
 * n = 10 in poi: lì il passo induttivo è a sua volta una disuguaglianza,
 * nella sola n, e la decide la tabella dei segni (capitolo 25). E gli
 * enunciati su una successione che l'enunciato stesso definisce per
 * ricorrenza, "sia a_0 = 0 e a_{n+1} = \sqrt{6 + a_n}; allora a_n < 3":
 * una formula per il termine n-esimo, oppure delle stime (capitolo 26). E
 * gli enunciati sulla derivata di una funzione, di ordine fisso o n-esima,
 * scritti con il segno di Leibniz (capitolo 27); senza il segno di uguale il
 * segno chiede la derivata, che il programma calcola e scrive. Dentro
 * un'espressione il segno è la derivata della funzione che lo segue: così
 * \{x \in \mathbb{R} \mid \frac{d}{dx}(f) > 0\} chiede dove f cresce, e lo
 * studio di una funzione lo decide la tabella dei segni. E i limiti,
 * \lim_{x \to 0} \frac{1 - \cos x}{x^2} = \frac{1}{2}, anche da un lato, a
 * \pm\infty, di successioni: con gli sviluppi in serie troncati, a
 * coefficienti esatti, e la scala delle crescite quando esponenziali,
 * potenze e logaritmi competono, come in e^x / x^5 o in \ln x / \ln \ln x
 * (capitolo 29). Senza il valore, \lim_{x \to a} f è una richiesta, e la
 * risposta è RISOLTO con il limite, oppure con il fatto che non esiste.
 *
 * Tratta altre tre famiglie di enunciati, ognuna con il suo metodo e con la
 * dimostrazione scritta per esteso:
 *
 *   - quelli sugli insiemi, come (S \setminus T) \setminus V = S \setminus
 *     (T \cup V), decisi esaminando le regioni di un diagramma di Venn
 *     (capitoli da 14 a 16);
 *   - quelli con quantificatori su insiemi di numeri, come "per ogni y in Z
 *     esiste x in Z con x + 5 = y", anche a proposito di un'applicazione
 *     definita da una formula: è così che si scrive che è iniettiva o
 *     suriettiva (capitoli da 17 a 19). Allo stesso modo l'enunciato può
 *     dichiarare un'operazione binaria con la sua regola, e dirla
 *     associativa o commutativa, o una relazione data da una regola, e
 *     dirla riflessiva o simmetrica: sempre per esteso, con la definizione.
 *     Un'ipotesi "esiste k" viene usata con il suo testimone, e così una
 *     congruenza il cui modulo è una lettera (18u). I divisori di un numero
 *     si provano tutti (18w), una potenza 2^{n} con n intero fa da lettera
 *     (18x), una relazione può legare coppie di numeri (17t), e i reali
 *     senza disuguaglianze si trattano con l'appartenenza a \mathbb{Q}
 *     (18y);
 *   - quelli su un insieme qualsiasi, con un'operazione, delle applicazioni
 *     o una relazione di cui si sa solo ciò che dicono le ipotesi: "un
 *     elemento neutro a sinistra e uno a destra coincidono". Si smentiscono
 *     con un modello finito, cercato anche con SAT (28t), e si dimostrano
 *     per saturazione di clausole con risoluzione e superposizione (28u),
 *     selezione SInE e casi AVATAR guidati dal SAT; i conflitti booleani
 *     vengono ricostruiti come risoluzioni nel certificato,
 *     oppure per assurdo, con istanze delle ipotesi e uguali al posto di uguali
 *     (17o in parser.c, capitolo 28);
 *     le istanze si scelgono dalla forma, e dove non basta con un modello
 *     candidato fatto degli elementi di cui si parla (28r).
 *     Le cardinalita dei modelli crescono entro budget di lavoro e memoria;
 *     variabili, sostituzioni, insiemi di variabili e scelte di parti hanno
 *     depositi dinamici, anche nella ricerca per istanze.
 *     Vi si scrive anche come nei libri: immagini f(X) e controimmagini
 *     f^{-1}(Y) di parti, relazioni come insiemi di coppie \{(x, y) \mid
 *     ...\}, le loro inverse e composizioni, uguaglianze e inclusioni tra
 *     insiemi, \exists!, coppie x \in S \times T (17p in parser.c). Il
 *     lettore svolge quella notazione nelle condizioni sugli elementi
 *     (17q), e lo svolgimento si ricontrolla sui modelli finiti (28h).
 *     Le relazioni e le applicazioni tra le parti di un insieme date da una
 *     regola, come (X, Y) \in G con X \cap Y = \emptyset, si svolgono invece
 *     in un enunciato del capitolo 14 (17r). E l'equipotenza, A \sim B: c'è
 *     una biiezione da A a B, e la si costruisce, con una grammatica piccola,
 *     da quelle delle ipotesi e dalla forma degli insiemi (17w in parser.c,
 *     28q): \mathcal{P}(S) \sim \mathcal{P}(T) e T_{1}^{S_{1}} \sim
 *     T_{2}^{S_{2}} da S \sim T e dai suoi simili.
 *
 * I metodi si combinano dove serve. Dentro un enunciato con quantificatori
 * un "per ogni n naturale" seguito da un'uguaglianza con somme viene
 * dimostrato per induzione: il metodo del capitolo 13 è una delle regole del
 * capitolo 18, e le espressioni sono le stesse in tutti e due. Gli enunciati
 * sugli insiemi restano invece un linguaggio a parte, e così quelli sugli
 * insiemi qualsiasi con i loro elementi.
 *
 * Il programma non si limita a dire vero o falso: risolve. Un enunciato della
 * forma \{x \in \mathbb{R} \mid condizione\} chiede per quali numeri reali
 * vale una condizione fatta di equazioni e disequazioni, e la risposta è
 * RISOLTO, con le soluzioni scritte come sui libri (x < -3 \lor x \ge 2). Le
 * trova la tabella dei segni (18p), che decide anche gli enunciati "per ogni
 * x reale"; di ciò che decide si può avere il grafico (18q). La condizione
 * può contenere radici quadrate e valori assoluti, esponenziali e logaritmi,
 * funzioni goniometriche: in quest'ultimo caso le soluzioni si ripetono, e
 * si scrivono con un intero k (x = \frac{\pi}{6} + 2k\pi). Con un parametro
 * reale accanto alla variabile, \forall a \in \mathbb{R}\ \{x \in \mathbb{R}
 * \mid condizione\}, le soluzioni sono un elenco di casi sul parametro, e la
 * tabella si fa in ognuno (18t). Allo stesso modo \{x \in \mathbb{Z} \mid
 * condizione\}, con una condizione fatta di congruenze, ha per risposta le
 * classi di resto delle soluzioni (18r).
 *
 * E gli integrali (capitolo 30). \int f \, dx = F + c dice che F è una
 * primitiva di f, e si dimostra derivando F con le regole del capitolo 27 e
 * riducendo F' - f a zero; \int f \, dx da solo chiede una primitiva, che il
 * programma cerca con i metodi dei libri (fratti semplici, per parti, per
 * sostituzione) e consegna, RISOLTO, solo dopo averla verificata allo stesso
 * modo. \int_{a}^{b} f \, dx = V si dimostra con il teorema fondamentale del
 * calcolo, dopo aver controllato con gli intervalli che f sia continua su
 * [a, b], e il valore si ricontrolla con una somma di Riemann. Gli
 * integrali impropri, con un estremo infinito o una funzione non limitata
 * vicino a un estremo o a un punto interno, valgono il limite della
 * primitiva agli estremi, calcolato con i limiti del capitolo 29, dopo che
 * la tabella dei segni ha mostrato le funzioni definite sull'intervallo
 * aperto; e l'enunciato può dire di valere +\infty o di convergere
 * (\in \mathbb{R}), che senza una primitiva si decide per confronto con
 * x^{-a} (\ln x)^{-b}.
 *
 * E l'algebra lineare sulle matrici scritte per esteso, con elementi
 * razionali (capitolo 31 in parser.c, capitolo 32): "il prodotto di queste
 * due matrici è quest'altra", il determinante, il rango, l'inversa, la
 * trasposta, le potenze. I due membri si calcolano con i razionali esatti e
 * l'eliminazione di Gauss, che di ogni determinante, rango e inversa lascia
 * un testimone: il verificatore li ricontrolla con soli prodotti, senza
 * eliminare. Un'espressione senza relazione chiede il suo valore, RISOLTO.
 * Con una lettera negli elementi, e la lettera nel suo insieme, un
 * determinante diventa il suo polinomio e l'enunciato passa alla tabella dei
 * segni: per quali valori di un parametro una matrice è singolare, quali
 * sono i suoi autovalori.
 *
 * E i sistemi lineari (paragrafo 31s in parser.c, capitolo 33): l'insieme
 * delle soluzioni, \{(x, y, z) \in \mathbb{R}^{3} \mid ...\}, è quello
 * scritto, è vuoto, contiene un vettore; da solo chiede le soluzioni,
 * RISOLTO, scritte come una soluzione particolare più i parametri liberi.
 * L'eliminazione di Gauss lascia anche qui dei testimoni, e il verificatore
 * moltiplica: una combinazione delle equazioni che dà 0 = c per il sistema
 * impossibile, due matrici G e T con G A + V T = I per dire che le
 * soluzioni sono tutte e sole quelle scritte. Con un parametro reale nei
 * coefficienti, \forall k \in \mathbb{R}\ davanti a un sistema o a un
 * rango ne chiede la discussione: l'elenco dei casi, uno per ogni valore
 * speciale del parametro e uno, con le formule in k, per tutti gli altri.
 * Dentro un enunciato, un rango o un insieme di soluzioni con il parametro
 * diventa la condizione su k che dice dove vale, e l'enunciato passa alla
 * tabella dei segni.
 *
 * E le funzioni di più variabili (capitolo 35): "f(x, y) = x^2 y \implies
 * \nabla f(1, 2) = (4, 1)", le derivate parziali scritte con \partial o con
 * il pedice, il gradiente e la matrice hessiana, come formule o in un punto,
 * e le uguaglianze che le derivate soddisfano (u_xx + u_yy = 0). Si deriva
 * con le regole del capitolo 27, una lettera alla volta, e ogni derivata,
 * anche mista, si ricontrolla con le serie di Taylor della funzione lungo
 * delle rette; senza il segno di uguale è una richiesta. In un punto le tesi
 * possono essere confronti tra numeri: "\nabla f(1, 1) = (0, 0) \land
 * \det H_{f}(1, 1) > 0 \land f_{xx}(1, 1) > 0" sono le condizioni che fanno
 * di (1, 1) un punto di minimo, scritte senza parole. E
 * "\{(x, y) \mid \nabla f(x, y) = (0, 0)\}" chiede i punti critici (capitolo
 * 36): il sistema lo risolve la tabella dei segni con un parametro, e ogni
 * punto trovato torna al capitolo 35 come enunciato.
 *
 * Gli enunciati arrivano da un file .tex (un \item per enunciato, capitolo 21)
 * oppure, senza argomenti, da una riga di stdin. Dopo la formula un \item può
 * dire da quale n vale l'enunciato; ciò che il programma non sa leggere lo
 * tratta come una condizione, e allora non dichiara falso l'enunciato. Su
 * richiesta dimostrazioni, soluzioni e grafici vengono scritti in un
 * documento LaTeX e compilati in PDF (capitolo 22).
 *
 * I FILE
 *
 * Il motore è un libro diviso in moduli, ognuno compilato per conto suo:
 *
 *   engine_*.c  il motore: cerca, calcola, decide, ricontrolla;
 *   parser.c    la lettura del LaTeX: dal testo agli alberi;
 *   output.c    il documento finale, con dimostrazioni, soluzioni e grafici;
 *   main.c      questo file: il programma a sé, con main();
 *   plot.c      i grafici: un piccolo matplotlib in C, che scrive PDF;
 *   checker.c   il verificatore indipendente dei certificati.
 *
 * Ogni modulo ha i suoi capitoli in NOME.c e la sua interfaccia in NOME.h:
 * ciò che gli altri moduli ne usano. Il resto è static, e fuori dal modulo
 * non si vede. L'elenco dei moduli segue l'indice dei capitoli. plot.c e
 * checker.c sono programmi a sé, che non sanno nulla degli altri, e di loro
 * si usa solo l'interfaccia.
 *
 * COME LO FA
 *
 *   testo LaTeX --[parsing, cap. 9]--> albero --[valutazione, cap. 11]-->
 *   frazione di polinomi --[induzione, cap. 13]--> verdetto
 *
 * Il parsing guarda solo i caratteri e costruisce l'albero sintattico. La
 * valutazione trasforma l'albero in una forma algebrica unica; l'induzione
 * valuta lo stesso albero tre volte, con n che vale n0, n e n+1.
 *
 * L'IDEA CENTRALE: SUCCESSIONI COME LETTERE
 *
 * Una somma S(n) = f(1) + ... + f(n) non ha in generale una formula chiusa, ma
 * per l'induzione non serve: basta sapere che S(n+1) = S(n) + f(n+1). Il
 * programma tratta quindi S(n) come una lettera nuova, un "atomo", e scrive
 * S(n+1) come atomo più l'ultimo termine. Lo stesso vale per i prodotti, per
 * n!, per 2^n, per i numeri di Fibonacci, per sin(n x): ognuno è un atomo, e
 * il suo valore in n+1 si scrive con gli atomi in n.
 *
 * Fatto questo, un enunciato L(n) = R(n) diventa una frazione di polinomi
 * D = L - R negli atomi, e l'induzione è algebra:
 *
 *   - caso base: con n = n0 somme e prodotti si svolgono termine per termine e
 *     D deve ridursi a zero;
 *   - passo: l'ipotesi induttiva D(n) = 0 permette di ricavare un atomo (di
 *     solito la somma) in funzione degli altri; sostituendolo in D(n+1) deve
 *     restare il polinomio nullo.
 *
 * Decidere se un polinomio è nullo è immediato: si guarda se ha termini.
 * Decidere che non lo è mai, per nessun n, è un'altra questione, e serve
 * per i divisori: vedi "Limiti di validità" più sotto.
 *
 * PERCHÉ QUESTE SCELTE
 *
 * Perché un albero e non la forma postfissa di prima. Lo stesso enunciato va
 * valutato con n legato a valori diversi e con l'indice k di una somma
 * sostituito da n+1: serve una struttura su cui tornare più volte, e la
 * ricorsione sull'albero è la più diretta. Gli enunciati sono corti, quindi la
 * profondità non è un problema.
 *
 * Perché non servono regole di "spostamento" per ogni funzione. Non c'è una
 * tabella che dica come si passa da n a n+1 per il fattoriale, per le potenze
 * o per il seno: basta rivalutare l'albero con n+1 al posto di n e portare
 * ogni risultato in forma canonica rispetto agli atomi in n. Le sole
 * conoscenze sono le definizioni (capitolo 10), scritte come dati.
 *
 * Perché frazioni non ridotte. Semplificare richiederebbe il massimo comun
 * divisore tra polinomi in più variabili. Per decidere un'uguaglianza basta
 * che il numeratore della differenza sia nullo.
 *
 * Perché gli esponenziali complessi. sin e cos si scrivono con e^{i x}; così
 * le formule di addizione e sin^2 + cos^2 = 1 non vanno insegnate al
 * programma: sono conseguenze dell'algebra degli esponenti (capitolo 11).
 *
 * Perché radici e logaritmi passano da una scomposizione in fattori. Una
 * radice è una potenza a esponente frazionario e un logaritmo trasforma i
 * prodotti in somme: scomponendo l'argomento in fattori di segno noto, la
 * radice di 12 e 2 per la radice di 3 diventano lo stesso monomio, e
 * ln(n+1) - ln(n) e ln(1 + 1/n) la stessa somma (capitoli 11 e 12).
 *
 * Perché il test di annullamento conosce il dominio, ma solo a volte. Una
 * derivata o una primitiva si affermano "dove i due membri sono definiti", e
 * lì valgono fatti che altrove sono falsi: dove \sqrt{x} è definita x >= 0,
 * e quindi \sqrt[3]{x} = (\sqrt[6]{x})^2 e \sqrt{x^2} = x. Il test di quelle
 * uguaglianze li usa (11q, 12d); nessun'altra decisione li vede, perché
 * parlerebbe anche dei punti in cui non valgono.
 *
 * COSA NON C'È ANCORA, E DOVE ANDREBBE
 *
 *   - Disuguaglianze con un parametro (Bernoulli con una lettera), o il cui
 *     passo induttivo non è un'espressione in n con sole radici quadrate:
 *     con un logaritmo, con la somma al quadrato, con un secondo membro che
 *     non cresce con n. Il metodo è nel capitolo 25, che dice che cosa
 *     servirebbe.
 *   - Valori assoluti fuori da un logaritmo: il parsing li riconosce; manca
 *     la regola di valutazione nel capitolo 11.
 *   - Identità tra i termini di una successione, come quella di Cassini per
 *     Fibonacci, F(n) F(n+2) - F(n+1)^2 = (-1)^{n+1}: gli atomi F(n) e F(n+1)
 *     sono trattati come lettere indipendenti. Servirebbe dimostrarle per
 *     induzione come lemmi e usarle nel test di annullamento (capitolo 12).
 *   - Somme il cui termine dipende anche da n: passando da n a n+1 cambiano
 *     tutti i termini, non solo l'ultimo. Fanno eccezione quelle con
 *     \binom{n}{k} per potenze con k all'esponente, che il teorema del
 *     binomio scrive in forma chiusa (11n); restano fuori k \binom{n}{k},
 *     due coefficienti binomiali nello stesso termine, e ogni altra
 *     dipendenza da n.
 *   - Enunciati in prosa: non sono una formula sola. Delle derivate si
 *     leggono quelle scritte con il segno di Leibniz, in testa alla
 *     formula o dentro un'espressione (capitolo 27), non f'(x); nelle
 *     formule n-esime mancano il doppio fattoriale e le funzioni che
 *     cambiano con n. Per confrontare una derivata con la forma stampata
 *     sui libri il test di annullamento usa i segni che dà il dominio
 *     (11q); mancano quelli che vengono da altro, come 1 - \cos x >= 0
 *     dall'immagine del coseno, e la radice di un prodotto di fattori il cui
 *     segno è noto ma che il conto non vede separati. Negli studi di
 *     funzione mancano gli esponenziali con l'esponente non di primo grado
 *     (e^{1/x}, e^{-x^2}: sono della tabella dei segni, 18p-8) e i punti in
 *     cui la funzione è definita da tutte e due le parti ma le regole non
 *     ne danno la derivata, come 0 per x|x| (27l): servirebbe il limite del
 *     rapporto incrementale.
 *     Fa eccezione la prosa di "sia ... allora ...", che definisce una
 *     successione per ricorrenza: il capitolo 21 la legge. Di una tale
 *     successione non si dimostrano ancora le tesi che non sono né una
 *     formula per a_n né una stima (vedi il capitolo 26).
 *   - Nei limiti: le stime per le divergenze con oscillazioni, due
 *     successioni per dire che un limite a \pm\infty non esiste, i
 *     parametri, le funzioni definite a pezzi; nella scala delle crescite,
 *     un esponenziale di un esponenziale come fattore e i logaritmi annidati
 *     più di una volta. Il capitolo 29 dice dove andrebbero.
 *   - Negli integrali: le aree, le primitive con arcoseno o funzioni
 *     iperboliche, la ricerca delle primitive delle radici di polinomi di
 *     secondo grado, i parametri; negli impropri, le oscillazioni
 *     (\int_0^{+\infty} \cos x \, dx) e i domini che la tabella dei segni
 *     non sa decidere. Il capitolo 30 dice dove andrebbero.
 *   - Negli enunciati con quantificatori: i numeri complessi scritti con dei
 *     numeri (1 + 2i) e le operazioni tra loro fuori dalla regola di
 *     un'applicazione; le disuguaglianze nella tesi insieme ad applicazioni
 *     tra interi o razionali, e tra più variabili; le applicazioni di due
 *     argomenti (tranne le operazioni scritte con un simbolo e quelle di
 *     \mathbb{C}, 17s), e quindi anche la scrittura 2^{m-1}(2n - 1) di ogni
 *     intero positivo; le coppie di coppie. Le applicazioni tra reali o tra
 *     complessi si svolgono nella loro definizione, e decide la tabella dei
 *     segni (18v-8): restano fuori le regole con divisioni per lettere,
 *     radici o funzioni, i parametri, le iterate, e le parti che dopo lo
 *     svolgimento hanno più lettere reali di quante la tabella ne decida,
 *     salvo gli "esiste" in testa a cui bastano dei razionali (18v-11). I
 *     reali senza disuguaglianze e senza applicazioni li trattano le regole
 *     del capitolo 18 (18y). Le applicazioni definite per casi tra interi e
 *     razionali, il valore assoluto nella loro regola e i valori in coppie
 *     ci sono (17s, 18v); di un enunciato con dei parametri (17s: anche
 *     dichiarati insieme, a, b \in \mathbb{Z}, e nascosti da una lettera
 *     legata con lo stesso nome) il motore dimostra la tesi per ogni valore
 *     dei parametri, distinguendo i casi che servono (18v-2), e la smentisce
 *     per ogni valore o per uno dei primi, mai con un valore cercato dalle
 *     condizioni. Nella teoria dei numeri mancano il massimo comun divisore,
 *     i numeri primi come insieme, il numero dei divisori di una lettera
 *     (quelli di un numero li prova tutti 18w), e le uguaglianze tra potenze
 *     della stessa base: x^{n m} = x non dà n m = 1, perché le potenze sono
 *     lettere indipendenti (18x), e così l'antisimmetria di "y è una potenza
 *     di x" resta fuori. La verifica del capitolo 19 non sa calcolare
 *     potenze di potenze troppo grandi, e allora non conferma. Il linguaggio
 *     è nel capitolo 17; ogni nuovo modo di ragionare è una regola in più
 *     nel capitolo 18. L'induzione vi entra solo per un "per ogni n" senza
 *     altre variabili intorno.
 *   - Negli enunciati su insiemi qualsiasi: le applicazioni e le parti da
 *     costruire, le ipotesi su tutte le parti di un insieme (\forall X
 *     \subseteq S tra le ipotesi, o in un'equivalenza), l'insieme delle
 *     parti come insieme di oggetti (le famiglie di parti, le partizioni),
 *     gli insiemi di applicazioni T^{S} come insiemi di oggetti, le
 *     relazioni scritte tra gli elementi (x \le y), la composizione come
 *     operazione, le potenze di un elemento. E un insieme qualsiasi insieme
 *     a un insieme numerico nello stesso enunciato: i due linguaggi non si
 *     parlano. L'equipotenza c'è (17w, 28q), e il numero di elementi di un
 *     insieme confrontato con un numero scritto, |S| = 3 (17x), che si dice
 *     con le sole variabili: "ci sono tre elementi distinti, e fra quattro
 *     due sono uguali". Non c'è con una lettera, |S| = n, e il verdetto lo
 *     dice (capitolo 20): contare chiederebbe l'induzione sul numero degli
 *     elementi, con le biiezioni che il passo chiede (S = S' \cup \{a\}), e
 *     dire infinito un insieme, per le sue parti numerabili, l'assioma della
 *     scelta numerabile. Vedi i capitoli 17 (17p, 17x) e 28.
 *   - Un certificato per tutto. Lo hanno le induzioni scritte con somme,
 *     prodotti, potenze, fattoriali, binomiali, successioni per ricorrenza
 *     e logaritmi, gli enunciati sugli insiemi senza "esiste", quelli su
 *     insiemi qualsiasi, dimostrati o smentiti, quelli della tabella dei
 *     segni con frazioni di polinomi e valori assoluti, le derivate, le
 *     primitive e gli integrali definiti (27m, 30cert), e i limiti calcolati
 *     con le serie (vedi "I certificati"). Non lo hanno le induzioni con
 *     radici, seni e arcotangenti, le tabelle dei segni con radici,
 *     esponenziali, logaritmi e funzioni goniometriche, o con un parametro,
 *     gli altri enunciati con quantificatori, i limiti decisi con l'algebra
 *     dei limiti (29g) o con un confronto tra costanti che il verificatore
 *     non sa fare, e gli integrali impropri: lì resta il solo controllo del
 *     motore su se stesso (numeri, campioni, passi riletti). Servirebbe
 *     che ogni regola del capitolo 18 emettesse un passo in una notazione
 *     che checker.c sappia ricontrollare. Anche "è definito per ogni n" è
 *     certificato solo in parte: non quando un divisore contiene una somma,
 *     un numero di Fibonacci o due potenze diverse come 3^n - 2^n, né quando
 *     lo si è stabilito con 13d, né quando c'è un logaritmo, di cui
 *     andrebbe certificato il segno dell'argomento.
 *
 * In tutti questi casi la risposta è NON SUPPORTATO, mai un verdetto inventato.
 *
 * LIMITI DI VALIDITÀ
 *
 * Un verdetto DIMOSTRATO per induzione vale per ogni n dal caso base in su, e
 * per i valori dei parametri in cui tutte le espressioni dell'enunciato sono
 * definite: denominatori non nulli, radicandi non negativi, argomenti dei
 * logaritmi positivi. I parametri, come x, sono numeri reali.
 *
 * L'induzione da sola non basta a dirlo: è algebra sulle lettere, e prova che
 * i due membri sono uguali "dove sono definiti". Tre controlli, tutti nel
 * capitolo 13, fanno il resto.
 *
 *   - Che quel "dove" esista (13e): servono dei valori dei parametri con cui
 *     i due membri si calcolano davvero, con i numeri, per i primi n. Così
 *     ln(-x) = ln(x) non risulta dimostrato: l'algebra lo accetta, perché
 *     tratta i logaritmi come ln|x|, ma non c'è un x in cui i due membri
 *     abbiano senso insieme. Se i numeri semplici non bastano, i valori da
 *     provare si ricavano dalle condizioni stesse dell'enunciato.
 *   - Che duri per ogni n (13c): con quei valori dei parametri, ogni
 *     divisione, radice e logaritmo deve avere senso per tutti gli n, non
 *     solo per i primi. (n - 50)/(n - 50) = 1 non risulta dimostrato, e il
 *     verdetto dice che per n = 50 c'è una divisione per zero. Se nessun
 *     valore fisso dei parametri va bene per ogni n, basta che per ogni n
 *     vadano bene tutti i valori abbastanza grandi (13d): è il caso della
 *     somma dei ln(x - k), definita per x > n.
 *   - Che un divisore non sia zero di nascosto: 2 cos(pi/3) - 1 è zero, ma
 *     l'algebra non lo riduce a zero. Un divisore conta come "diverso da
 *     zero" solo se una regola lo prova.
 *
 * Quando uno di questi controlli non sa decidere, il verdetto è NON
 * DIMOSTRATO. Capita anche con enunciati veri: le regole di 13c conoscono i
 * polinomi in n e in potenze come 2^n, i segni evidenti, il segno di un seno
 * o di un coseno dal suo quadrante. Non sanno dire che n! - 5 non si annulla,
 * né il segno di un'espressione trigonometrica che non sia un solo seno o
 * coseno, né quello di ln 3 - 1: lì servirebbero altre regole.
 *
 * Negli enunciati con quantificatori questa riserva non c'è: ogni variabile
 * ha il suo insieme, e che nessun divisore si annulli lì fa parte di ciò che
 * viene dimostrato (capitolo 18).
 *
 * LE DIMOSTRAZIONI SCRITTE
 *
 * Ogni verdetto DIMOSTRATO ha la sua dimostrazione scritta, e ciò che vi è
 * scritto viene ricontrollato per una strada diversa da quella che lo ha
 * prodotto. Per gli insiemi e per i quantificatori si ricontrolla ogni fatto
 * prima di scriverlo (16h, 16i e i controlli del capitolo 18); per gli
 * insiemi qualsiasi ogni passo viene riletto con un metodo diverso da quello
 * che l'ha trovato (28e); per i limiti la funzione viene ricalcolata con gli
 * intervalli vicino al punto, e ogni valore scritto viene riletto (29i,
 * 29j); per gli integrali impropri la primitiva viene ricontrollata con le
 * somme di Riemann su intervalli che si allargano verso gli estremi, e la
 * convergenza con il confronto (30k). Per
 * l'induzione si fa di più: ogni formula scritta viene riletta dal testo,
 * con il parser degli enunciati, e ricalcolata con i numeri (13g). Una
 * dimostrazione che non supera il controllo non viene stampata.
 *
 * Le frasi che collegano i fatti ("quindi", "holds", "fails") sono scritte
 * dal programma secondo schemi fissi: non c'è un controllo automatico che le
 * capisca. Le fissano i test, con una frase attesa per ogni combinazione di
 * uguale e diverso, affermato e negato (tests/engine).
 *
 * LE SPIEGAZIONI
 *
 * Una dimostrazione dice perché; chi studia vuole anche vedere come ci si
 * arriva. Di un'equazione o disequazione razionale decisa con la tabella dei
 * segni il motore registra perciò anche la strada (capitolo 40): la
 * differenza dei due membri, la stessa come una sola frazione, i suoi
 * fattori, gli zeri di ognuno, la tabella con una riga per fattore, i due
 * membri calcolati in un valore di ogni intervallo. Sono dati, non frasi: le
 * frasi le mette il documento (capitolo 41, in output.c), una per tipo di
 * passo. Ogni passaggio registrato è ricontrollato a partire dal testo che
 * verrà stampato, riletto e ricalcolato per un'altra strada; uno che non
 * regge non si mostra, e conta tra i passi non giustificati. La spiegazione
 * viene dopo il verdetto e non lo cambia. Allo stesso modo una derivata
 * richiesta si spiega una regola alla volta (27n): la derivata di ogni
 * pezzo dell'espressione, dal più interno, e ogni riga la ricontrolla
 * checker.c. E di un'uguaglianza dimostrata per induzione si registrano i
 * primi valori dei due membri, che diventano una tabella e un grafico, e
 * il passo induttivo svolto riga per riga (40b). Le spiegazioni entrano
 * nel documento di --proofs; chi vuole il documento con le sole
 * dimostrazioni lo chiede con --plain-proofs.
 *
 * I CERTIFICATI
 *
 * I controlli descritti fin qui sono del programma su se stesso: un errore
 * nella sua aritmetica o nel suo modo di leggere le formule li attraversa
 * tutti. Per questo una dimostrazione per induzione viene anche consegnata,
 * come certificato, a un secondo programma: checker.c, che ha la sua
 * aritmetica e i suoi polinomi, non usa nulla del motore, ed è abbastanza
 * piccolo da poterlo leggere tutto (13h). Se lo respinge, il verdetto è NON
 * DIMOSTRATO. Per un enunciato sugli insiemi il certificato è il solo
 * enunciato: il verificatore lo decide da capo, con un conto suo sulle
 * regioni del diagramma di Venn (prove_sets()). Per un enunciato su insiemi
 * qualsiasi (28f) il certificato è il modello finito che lo smentisce, o
 * l'esempio che chiede, su cui il verificatore ricalcola l'enunciato; oppure,
 * per una dimostrazione, i nomi e le istanze usati, con le applicazioni
 * definite di un'equipotenza (28q), di cui il verificatore controlla da sé la
 * forma, e con un conto finito che portino a una contraddizione anche quando
 * qualche insieme è vuoto. Lì il verdetto, DIMOSTRATO o FALSO,
 * vuole che il certificato sia accettato. Per un enunciato deciso con la
 * tabella dei segni (18p-15) il certificato è la tabella: il verificatore ne
 * ricava da capo i polinomi, ne riconta le radici con Sturm, ricalcola la
 * verità di ogni riga e rilegge le soluzioni scritte; DIMOSTRATO, FALSO e
 * RISOLTO vogliono che lo accetti, e se non sa controllarlo il verdetto resta
 * e dice perché il certificato manca. Per una derivata, una primitiva o un
 * integrale definito (27m, 30cert) il certificato porta le espressioni, e il
 * verificatore deriva da sé, con regole sue, e decide con la sua algebra se
 * la differenza è zero; per un integrale ricontrolla anche, con Sturm, che le
 * funzioni siano definite su tutto l'intervallo, e il valore F(b) - F(a).
 * Anche lì un rifiuto rende il verdetto NON DIMOSTRATO. Lo stesso per un
 * limite (29n): il certificato è l'enunciato con la sostituzione e la
 * precisione di ogni lato, e il verificatore rifà gli sviluppi in serie con
 * la sua aritmetica. Per un'identità con gli indici del calcolo tensoriale
 * (38e) il certificato è l'enunciato con la dimensione, e il verificatore
 * rifà il conto su tutti i valori degli indici: DIMOSTRATO e FALSO vogliono
 * che lo accetti. Con una metrica dichiarata (capitolo 39) il certificato è
 * dell'identità svolta, e che sia la stessa di quella scritta lo ricontrolla
 * il motore (38d), non il verificatore. Le componenti di un tensore dato da
 * una tabella vanno nel certificato come dati (38g).
 *
 * Il certificato dimostra una cosa precisa, enunciata in testa a checker.c,
 * e non di più. La sua parte principale dice che per ogni n dal caso base in
 * su i due membri sono uguali, dove l'enunciato è definito fino a quel n.
 * Una seconda parte, quando c'è, dice che l'enunciato è definito per ogni n
 * nel punto dei parametri trovato da 13c: il verificatore lo ricontrolla con
 * regole sue, e se trova un n in cui un divisore si annulla respinge. Quando
 * quelle regole non bastano, la seconda parte manca, e "definito per ogni n"
 * resta un controllo del solo motore. Resta sempre fuori la lettura del
 * LaTeX: l'enunciato compare nel certificato riscritto nella sua notazione,
 * e chi vuole può confrontarlo.
 *
 * Il verdetto dice sempre che cosa il certificato copre: "definiti e uguali
 * per ogni n", "uguali dove sono definiti", oppure "senza certificato", con
 * il motivo quando è un'induzione, una tabella dei segni, una derivata, un
 * integrale o un limite.
 *
 * LO STATO È DI OGNI THREAD
 *
 * Il motore decide un enunciato alla volta, e tra un passo e l'altro tiene
 * il suo stato in variabili dei moduli: l'arena, la tabella degli atomi, le
 * condizioni raccolte, il motivo di un fallimento, i budget. Ogni variabile
 * di durata statica dei moduli, del verificatore e dei grafici, comprese
 * quelle static dentro le funzioni, è _Thread_local: ogni thread ha il suo
 * motore, che non vede gli altri. Le due arene, quella del motore
 * (ARENA_BYTES) e quella del verificatore (CK_ARENA_BYTES), sono troppo
 * grandi per stare tra le variabili di thread, che il sistema copia per
 * intero in ogni thread nuovo: sono memoria presa la prima volta che servono.
 * Un thread chiama engine_init() prima di ogni altra cosa, e i valori delle
 * opzioni (--model-work, --stack-budget, ...) sono anch'essi suoi: chi gliele
 * vuole dare le copia (settings_apply()).
 *
 * Che non sia rimasta una variabile condivisa lo dicono i file oggetto: con
 * tutto lo stato di thread, nelle sezioni __data, __bss e common dei moduli
 * non resta nessun simbolo, solo costanti. E lo dice ThreadSanitizer, con
 * --threads su una parte del corpus.
 *
 * Non vuol dire che il motore sia rientrante nello stesso thread: ciò che
 * tiene del suo ultimo verdetto, per il documento, lo cancella la chiamata
 * dopo (vedi Math/Engine.h). Vuol dire che più thread possono decidere
 * enunciati insieme, ognuno con il suo stato; è ciò che fa --threads.
 *
 * COMPILAZIONE
 *
 * La fa CMake, con il resto di Vampire. Ogni modulo è un'unità di
 * compilazione dell'obiettivo mathengine; questo file, con quei moduli, dà
 * il programma a sé (l'obiettivo quaerens), che legge gli stessi enunciati
 * senza Vampire.
 *
 * Servono GCC o Clang: i conti esatti usano __int128. Il verificatore si
 * compila anche da solo (vedi la testa di checker.c). Per avere il
 * documento finale in PDF serve inoltre un compilatore LaTeX installato
 * (tectonic oppure pdflatex); senza, il programma scrive comunque il
 * documento .tex e il PDF dei grafici.
 *
 * INDICE DEI CAPITOLI
 *
 * La numerazione è una sola per tutti i moduli. I capitoli segnati con un
 * nome di file stanno in quel file; gli altri nei moduli engine_*.c, come
 * dice l'elenco che segue l'indice. Il capitolo 18, il più lungo, è
 * diviso in capitoli numerati 18.1, 18.2, ...: le sue regole si citano come
 * 18a, 18p, 18t-h, e con la sottonumerazione restano tutte nel capitolo che
 * dà loro il nome.
 *
 *    1. Include e limiti
 *    2. Errori e memoria
 *    3. Numeri esatti: razionali e razionali complessi
 *    4. Monomi e atomi
 *    5. Polinomi negli atomi
 *    6. Creazione degli atomi
 *    7. Frazioni di polinomi
 *    8. Albero sintattico                                   (parser.c)
 *    9. Parsing: dal LaTeX all'albero                       (parser.c)
 *   14. Insiemi: notazione e albero                         (parser.c)
 *   17. Quantificatori: notazione e albero                  (parser.c)
 *   31. Matrici: notazione e albero                         (parser.c)
 *   21. Lettura degli enunciati da un file .tex             (parser.c)
 *   34. Funzioni di più variabili: notazione e albero       (parser.c)
 *   37. Indici: notazione e albero                          (parser.c)
 *   39. Indici: metrica e componenti dichiarate             (parser.c)
 *   10. Vocabolario: le successioni note, come dati
 *   11. Valutazione: dall'albero alla frazione
 *   12. Test di annullamento
 *   13. Induzione: caso base, passo, verdetto
 *   15. Insiemi: decisione per regioni
 *   16. Insiemi: verifica indipendente e dimostrazione scritta
 *   24. Intervalli: numeri reali con l'errore garantito
 *   18. Quantificatori: regole di dimostrazione
 *       18.1   Lo stato della dimostrazione e la scrittura dei polinomi
 *       18.2   Polinomi nelle variabili generiche: zeri, segni, interi
 *       18.3   Confronti e disgiunzioni di confronti
 *       18.4   "Per ogni" ed "esiste": induzione, casi, equazioni
 *       18.5   Le ipotesi "esiste", con il loro testimone
 *       18.6   establish(): la dimostrazione per struttura
 *       18.7   Sole congruenze: tutti i resti
 *       18.8   La tabella dei segni: numeri e polinomi esatti, i punti
 *       18.9   Le lettere della tabella: esponenziali, logaritmi, goniometria
 *       18.10  L'albero dei segni
 *       18.11  I confronti preparati, e la loro verità in una riga
 *       18.12  Il controllo con i numeri
 *       18.13  Le righe della tabella e le soluzioni
 *       18.14  Le soluzioni di una condizione periodica
 *       18.15  Il grafico della tabella dei segni
 *       18.16  Il verdetto della tabella e il suo certificato
 *       18.17  Un parametro: la proiezione e le celle
 *       18.18  Un parametro: le celle decise e scritte
 *       18.19  Un parametro: i controlli e il verdetto
 *   40. La spiegazione: i passaggi registrati e ricontrollati
 *   19. Quantificatori: verifica indipendente e verdetto
 *   25. Induzione su una disuguaglianza
 *   26. Successioni definite per ricorrenza
 *   27. Derivate: dimostrarle, calcolarle, usarle negli studi di funzione
 *   28. Insiemi qualsiasi: modelli finiti anche con SAT, istanze, uguali al posto di uguali
 *   29. Limiti
 *   30. Integrali: primitive, integrali definiti e impropri
 *   32. Algebra lineare esatta: matrici a elementi razionali
 *   33. Sistemi lineari: l'insieme delle soluzioni, anche con un parametro
 *   35. Funzioni di più variabili: derivate parziali, gradiente, hessiana
 *   36. Punti critici, e l'ingresso delle funzioni di più variabili
 *   38. Identità con gli indici: il conto su tutti i valori
 *   20. Dimostrare un enunciato
 *   41. La spiegazione scritta                              (output.c)
 *   22. Il documento finale                                 (output.c)
 *   23. main
 */

/* I MODULI DEL MOTORE
 *
 * Il libro è diviso in moduli, ognuno un'unità di compilazione con la sua
 * interfaccia: NOME.c ha i capitoli, NOME.h ciò che gli altri moduli ne
 * usano. Un capitolo usa ancora ciò che i capitoli sopra di lui hanno
 * presentato, e lo riceve includendo l'interfaccia del modulo che lo
 * contiene. In ordine di lettura:
 *
 *   engine_foundations
 *       limiti, errori e memoria, numeri esatti, monomi, polinomi,
 *       atomi, frazioni di polinomi (capitoli 1-7)
 *   parser
 *       la lettura del LaTeX: gli alberi delle espressioni, degli
 *       enunciati sugli insiemi, di quelli con quantificatori, delle
 *       matrici e degli indici, i lettori che li costruiscono, gli
 *       \item di un file (capitoli 8, 9, 14, 17, 21, 31, 34, 37 e
 *       39)
 *   engine_evaluation
 *       le successioni note come dati, la valutazione di un albero
 *       in una frazione, i test di annullamento (capitoli 10-12)
 *   engine_induction
 *       induzione su somme e prodotti: caso base, passo, verdetto
 *       (capitolo 13)
 *   engine_sets
 *       relazioni tra insiemi: decisione per regioni, verifica
 *       indipendente, dimostrazione scritta (capitoli 15-16)
 *   engine_intervals
 *       i numeri reali come intervalli con l'errore garantito
 *       (capitolo 24)
 *   engine_quantifiers
 *       enunciati con quantificatori sui numeri: le regole di
 *       dimostrazione (capitoli da 18 a 18.7)
 *   engine_sign_tables
 *       la tabella dei segni: punti esatti, segni, righe, soluzioni,
 *       grafici, un parametro (capitoli 18.8-18.19)
 *   engine_explanation
 *       la spiegazione: i passaggi registrati e ricontrollati
 *       (capitolo 40)
 *   engine_quantifiers_verdict
 *       enunciati con quantificatori: verifica indipendente e
 *       verdetto (capitolo 19)
 *   engine_sequences
 *       induzione su una disuguaglianza, successioni definite per
 *       ricorrenza (capitoli 25-26)
 *   engine_derivatives
 *       derivate: dimostrarle, calcolarle, usarle negli studi di
 *       funzione (capitolo 27)
 *   engine_logic
 *       insiemi qualsiasi: modelli finiti, istanze, saturazione, e i
 *       compiti svolti per Vampire (capitolo 28)
 *   engine_limits
 *       limiti (capitolo 29)
 *   engine_integrals
 *       integrali: primitive, integrali definiti e impropri
 *       (capitolo 30)
 *   engine_linear_algebra
 *       algebra lineare esatta: matrici, determinanti, sistemi
 *       lineari (capitoli 32-33)
 *   engine_multivariable
 *       funzioni di più variabili: derivate parziali, gradiente,
 *       hessiana, punti critici (capitoli 35-36)
 *   engine_indices
 *       identità con gli indici: il conto su tutti i valori
 *       (capitolo 38)
 *   engine_statement
 *       dimostrare un enunciato: quale capitolo lo legge, e il
 *       verdetto (capitolo 20)
 *   output
 *       il documento finale: enunciati, spiegazioni, dimostrazioni,
 *       soluzioni e grafici in LaTeX, e la sua compilazione in PDF
 *       (capitoli 41 e 22)
 *
 * Questo file è il programma a sé: l'ultimo capitolo, con main(). Vampire
 * non lo compila: usa i moduli attraverso Math/Engine.h. */
#include <pthread.h>
#include <stdatomic.h>

#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"
#include "engine_sign_tables.h"
#include "engine_explanation.h"
#include "engine_statement.h"
#include "output.h"

/* =============================================================================
 * 23. MAIN
 * ============================================================================
 *
 * Modi d'uso:
 *
 *     mathresearcher FILE.tex ...                  dimostra o risolve ogni enunciato dei file
 *     mathresearcher --proofs OUT.pdf FILE.tex ... scrive anche il documento con le
 *                                                  dimostrazioni, le soluzioni e i grafici:
 *                                                  in LaTeX (OUT.tex, con i grafici in
 *                                                  OUT-plots.pdf) e compilato in PDF; dove
 *                                                  il motore ha registrato i passaggi, ogni
 *                                                  voce comincia con lo svolgimento
 *     mathresearcher --plain-proofs OUT.pdf FILE.tex ...
 *                                                  lo stesso documento senza gli svolgimenti:
 *                                                  le sole dimostrazioni, con i grafici
 *     mathresearcher --certificates OUT FILE.tex ...
 *                                                  scrive anche i certificati verificati,
 *                                                  da far ricontrollare a checker
 *     mathresearcher --threads N FILE.tex ...      gli enunciati di un file in N thread
 *                                                  insieme, senza documento: le stesse righe,
 *                                                  nello stesso ordine
 *     mathresearcher                               legge un enunciato da stdin
 *
 * --model-work N e --model-memory BYTES regolano i budget della ricerca SAT
 * (20.000.000 operazioni e 128 MiB di default), non un massimo di elementi.
 * --model-steps N regola gli elementi che i quantificatori provano
 * ricalcolando un enunciato sui modelli (40.000.000 di default): un modello
 * che non si riesce a ricalcolare non è un controesempio, e il verdetto lo dice.
 * Il verificatore riceve due volte e mezza quel budget.
 * --stack-budget BYTES regola la pila concessa agli alberi di un enunciato
 * lungo (4 MiB di default, per una pila di 8 MB): oltre, l'esito è "pila di
 * lavoro esaurita".
 * --verification-work N regola le visite del verificatore numerico
 * (20.000.000 di default): una verifica interrotta non conferma nulla.
 * --saturation-work N e --saturation-memory BYTES regolano le visite e la
 * memoria della ricerca per clausole (2.000.000 e 128 MiB di default).
 * Tutte le opzioni si possono dare insieme. Il codice di uscita è 0 se tutti
 * gli enunciati sono stati dimostrati o risolti, 1 altrimenti.
 */

/* Conteggio dei verdetti su un file. */
typedef struct {
    int total;        /* \item trovati */
    int proved;
    int certified;    /* tra i dimostrati, quelli con il certificato verificato */
    int refuted;
    int not_proved;
    int unsupported;
    int solved;       /* insiemi di soluzioni trovati */
} Report;

/* Dimostra tutti gli enunciati del file path. Riempie *report con i conteggi
 * e, se out non è NULL, vi scrive una riga per enunciato. Se document non è
 * NULL vi scrive, come elenco, ogni enunciato con la sua dimostrazione e il
 * suo grafico; se certificates non è NULL vi scrive i certificati
 * verificati, uno dopo l'altro. Ritorna 0 se il file non si può leggere, 1
 * altrimenti. */
static int prove_file(const char *path, Report *report, FILE *out, Document *document, FILE *certificates) {
    memset(report, 0, sizeof *report);
    char *text = read_file(path);
    if (!text) return 0;

    if (document) document_list(document, 1);
    const char *position = text, *item, *end;
    while (next_item(&position, &item, &end)) {
        Verdict verdict = prove_item(item, end);
        report->total++;
        switch (verdict.outcome) {
        case PROVED:      report->proved++; break;
        case REFUTED:     report->refuted++; break;
        case NOT_PROVED:  report->not_proved++; break;
        case UNSUPPORTED: report->unsupported++; break;
        case SOLVED:      report->solved++; break;
        }
        if (verdict.certificate) {
            if (verdict.outcome == PROVED) report->certified++;
            if (certificates) fprintf(certificates, "%s\n", verdict.certificate);
        }
        if (out) {
            fprintf(out, "%4d. ", report->total);
            verdict_print(out, &verdict);
            fputc('\n', out);
        }

        /* Nel documento l'enunciato va com'è scritto nel file: lo si rilegge
         * dal testo, perché prove_item() ne ritorna solo il verdetto. */
        if (document) {
            Item statement;
            const char *unreadable = read_item(item, end, &statement);
            document_item(document, unreadable ? NULL : statement.formula, &verdict, figure, &explanation);
        }
    }
    if (document) document_list(document, 0);
    free(text);
    return 1;
}

/* --threads N. Lo stato del motore è di ogni thread (vedi engine_names.h):
 * N thread decidono gli enunciati di un file insieme, ognuno con il suo,
 * e le righe si scrivono dopo, nell'ordine del file, come le scrive
 * prove_file(). Un enunciato non dipende da quelli prima di lui; ciò che
 * il motore tiene del suo ultimo verdetto, per il documento, resta nel
 * thread che l'ha deciso, e per questo con il documento non si usa.
 *
 * Le opzioni sono variabili di ogni thread, come tutto lo stato: ognuno
 * prende quelle del thread principale prima di cominciare. */
typedef struct {
    size_t stack_budget, model_memory_limit, saturation_memory_limit;
    unsigned long long model_work_limit, saturation_work_limit, verification_work_limit;
    long long model_step_limit;
} Settings;

typedef struct {
    const char *item, *end;
    int outcome, certified;
    char *line, *certificate;   /* sullo heap, scritti dal thread che l'ha deciso */
} Job;

typedef struct {
    Job *jobs;
    int count;
    atomic_int next;
    atomic_int unjustified;     /* i passi scartati, sommati da tutti i thread */
    Settings settings;
} Pool;

static Settings settings_now(void) {
    return (Settings){stack_budget, model_memory_limit, saturation_memory_limit, model_work_limit,
                      saturation_work_limit, verification_work_limit, model_step_limit};
}

static void settings_apply(const Settings *s) {
    stack_budget = s->stack_budget; model_memory_limit = s->model_memory_limit;
    saturation_memory_limit = s->saturation_memory_limit; model_work_limit = s->model_work_limit;
    saturation_work_limit = s->saturation_work_limit; verification_work_limit = s->verification_work_limit;
    model_step_limit = s->model_step_limit;
}

static void *prove_jobs(void *argument) {
    Pool *pool = argument;
    engine_init();
    settings_apply(&pool->settings);
    for (int i; (i = atomic_fetch_add(&pool->next, 1)) < pool->count;) {
        Job *job = &pool->jobs[i];
        Verdict verdict = prove_item(job->item, job->end);
        size_t length = 0;
        FILE *line = open_memstream(&job->line, &length);
        if (line) { verdict_print(line, &verdict); fclose(line); }
        job->outcome = verdict.outcome;
        job->certified = verdict.certificate != NULL;
        job->certificate = verdict.certificate ? strdup(verdict.certificate) : NULL;
    }
    atomic_fetch_add(&pool->unjustified, unjustified_steps);
    return NULL;
}

/* Come prove_file(), senza documento, con threads thread. La pila di ogni
 * thread è grande come quella del programma: il budget della pila
 * (--stack-budget) ne è la metà. */
static int prove_file_threads(const char *path, Report *report, FILE *out, FILE *certificates, int threads) {
    memset(report, 0, sizeof *report);
    char *text = read_file(path);
    if (!text) return 0;
    Pool pool = {.settings = settings_now()};
    atomic_init(&pool.next, 0);
    atomic_init(&pool.unjustified, 0);
    const char *position = text, *item, *end;
    int capacity = 0;
    while (next_item(&position, &item, &end)) {
        if (pool.count == capacity) {
            capacity = capacity ? 2 * capacity : 64;
            Job *grown = realloc(pool.jobs, (size_t)capacity * sizeof *grown);
            if (!grown) { free(pool.jobs); free(text); return 0; }
            pool.jobs = grown;
        }
        pool.jobs[pool.count++] = (Job){item, end, 0, 0, NULL, NULL};
    }
    pthread_attr_t attributes;
    pthread_attr_init(&attributes);
    size_t stack = 2 * stack_budget + ((size_t)8 << 20);
    pthread_attr_setstacksize(&attributes, stack);
    pthread_t *workers = calloc((size_t)threads, sizeof *workers);
    int started = 0;
    for (; workers && started < threads; started++)
        if (pthread_create(&workers[started], &attributes, prove_jobs, &pool) != 0) break;
    if (!started) prove_jobs(&pool);   /* nessun thread: si fa qui, come senza l'opzione */
    for (int i = 0; i < started; i++) pthread_join(workers[i], NULL);
    pthread_attr_destroy(&attributes);
    free(workers);
    unjustified_steps += atomic_load(&pool.unjustified);

    for (int i = 0; i < pool.count; i++) {
        Job *job = &pool.jobs[i];
        report->total++;
        switch (job->outcome) {
        case PROVED:      report->proved++; break;
        case REFUTED:     report->refuted++; break;
        case NOT_PROVED:  report->not_proved++; break;
        case UNSUPPORTED: report->unsupported++; break;
        case SOLVED:      report->solved++; break;
        }
        if (job->certified) {
            if (job->outcome == PROVED) report->certified++;
            if (certificates) fprintf(certificates, "%s\n", job->certificate);
        }
        if (out) fprintf(out, "%4d. %s\n", report->total, job->line ? job->line : "");
        free(job->line);
        free(job->certificate);
    }
    free(pool.jobs);
    free(text);
    return 1;
}

/* Legge un budget decimale positivo senza conversioni con trabocco. */
static int read_model_budget(const char *text, unsigned long long *value) {
    unsigned long long n = 0;
    if (!*text) return 0;
    for (; *text; text++) {
        if (*text < '0' || *text > '9' || n > (ULLONG_MAX - (unsigned)(*text - '0')) / 10) return 0;
        n = 10 * n + (unsigned)(*text - '0');
    }
    *value = n;
    return n != 0;
}

/* Legge una riga completa da stream in memoria posseduta dal chiamante,
 * da liberare dopo l'uso. Non tronca l'input a un buffer numerico interno.
 * NULL indica EOF prima della riga oppure errore di risorse in failure. */
static char *read_input_line(FILE *stream) {
    char *line=NULL;size_t length=0,capacity=0;int ch;
    while ((ch=fgetc(stream))!=EOF && ch!='\n') {
        if (length>(size_t)-1-2 || !work_reserve((void **)&line,&capacity,length+2,1)) {
            free(line);fail(OUT_OF_MEMORY);return NULL;
        }
        line[length++]=(char)ch;
    }
    /* Un errore dello stream non e la fine di una formula: il prefisso gia
     * letto non deve diventare un enunciato diverso da quello ricevuto. */
    if (ferror(stream)) { free(line);fail("errore durante la lettura dell'enunciato");return NULL; }
    if (ch==EOF && !length) { free(line);return NULL; }
    if (!work_reserve((void **)&line,&capacity,length+1,1)) { free(line);return NULL; }
    line[length]=0;return line;
}

int main(int argc, char **argv) {
    engine_init();
    int threads = 0;

    /* Senza argomenti: un solo enunciato da stdin, con la sua dimostrazione. */
    if (argc < 2) {
        printf("Enunciato in LaTeX: ");
        char *line=read_input_line(stdin);
        if (!line) { if (failure) fprintf(stderr,"ERRORE: %s\n",failure); return 1; }
        Verdict verdict = prove(line, 'n', 0, 0);
        verdict_print(stdout, &verdict);
        putchar('\n');
        if (verdict.proof) printf("\n%s\n", verdict.proof);
        free(line);
        return verdict.outcome == PROVED || verdict.outcome == SOLVED ? 0 : 1;
    }

    /* Le opzioni, prima dei file.
     *
     * --proofs: il documento finale (capitolo 22). Chiederlo è anche ciò che
     * fa costruire i grafici e le spiegazioni (capitolo 40): senza un
     * documento non servono.
     *
     * --plain-proofs: lo stesso documento senza le spiegazioni, con le sole
     * dimostrazioni e i grafici delle tabelle dei segni: quello che il
     * programma scriveva prima del capitolo 40. È un'opzione a sé, e non un
     * valore in più di --proofs, perché le opzioni si leggono a coppie, un
     * nome e il suo valore: così prende il file allo stesso modo. Le due non
     * si danno insieme: il documento è uno.
     *
     * --certificates: il file in cui scrivere i certificati. */
    FILE *certificates = NULL;
    Document document;
    int first = 1, documented = 0;
    for (; first + 1 < argc && strncmp(argv[first], "--", 2) == 0; first += 2) {
        if (strcmp(argv[first], "--model-work") == 0 || strcmp(argv[first], "--model-memory") == 0 ||
            strcmp(argv[first], "--stack-budget") == 0 || strcmp(argv[first], "--model-steps") == 0 || strcmp(argv[first], "--verification-work") == 0 || strcmp(argv[first], "--saturation-work") == 0 ||
            strcmp(argv[first], "--saturation-memory") == 0) {
            unsigned long long budget;
            int stack = strcmp(argv[first], "--stack-budget") == 0;
            int memory = stack || strcmp(argv[first], "--model-memory") == 0 || strcmp(argv[first], "--saturation-memory") == 0;
            int steps = strcmp(argv[first], "--model-steps") == 0;
            if (!read_model_budget(argv[first + 1], &budget) || (memory && budget > (size_t)-1) || (steps && budget >= LLONG_MAX)) {
                printf("ERRORE: budget positivo non rappresentabile: %s\n", argv[first + 1]); return 1;
            }
            if (stack) stack_budget = (size_t)budget;
            else if (strcmp(argv[first], "--saturation-memory") == 0) saturation_memory_limit = (size_t)budget;
            else if (strcmp(argv[first], "--saturation-work") == 0) saturation_work_limit = budget;
            else if (memory) model_memory_limit = (size_t)budget;
            else if (steps) model_step_limit = (long long)budget;
            else if (strcmp(argv[first], "--verification-work") == 0) verification_work_limit = budget;
            else model_work_limit = budget;
            continue;
        }
        if (strcmp(argv[first], "--threads") == 0 && !threads) {
            unsigned long long count = 0;
            if (!read_model_budget(argv[first + 1], &count) || count > 256) { printf("ERRORE: da 1 a 256 thread: %s\n", argv[first + 1]); return 1; }
            threads = (int)count;
            continue;
        }
        if (strcmp(argv[first], "--certificates") == 0 && !certificates) {
            certificates = fopen(argv[first + 1], "w");
            if (!certificates) { printf("ERRORE: impossibile scrivere %s\n", argv[first + 1]); return 1; }
            continue;
        }
        int worked = strcmp(argv[first], "--proofs") == 0;
        if ((!worked && strcmp(argv[first], "--plain-proofs") != 0) || documented) { printf("ERRORE: opzione sconosciuta o ripetuta: %s\n", argv[first]); return 1; }
        const char *problem = document_open(&document, argv[first + 1]);
        if (problem) { printf("ERRORE: %s: %s\n", problem, argv[first + 1]); return 1; }

        /* Tutti e due i segnali si assegnano, non solo quello che si
         * accende: il documento asciutto deve esserlo anche se qualcuno ha
         * già chiesto le spiegazioni. */
        documented = figures_wanted = 1;
        explanations_wanted = worked;
    }

    /* Un file per argomento. */
    int all_proved = 1;
    for (int i = first; i < argc; i++) {
        Report report;
        printf("%s\n", argv[i]);
        if (documented) document_section(&document, argv[i]);
        int read = threads > 1 && !documented ? prove_file_threads(argv[i], &report, stdout, certificates, threads)
                                              : prove_file(argv[i], &report, stdout, documented ? &document : NULL, certificates);
        if (!read) {
            printf("ERRORE: impossibile leggere il file\n");
            all_proved = 0;
            continue;
        }
        printf("Riepilogo: %d enunciati, %d dimostrati (%d con certificato verificato), %d falsi, %d non dimostrati, %d non supportati",
               report.total, report.proved, report.certified, report.refuted, report.not_proved, report.unsupported);

        /* Gli insiemi di soluzioni si contano solo se ce ne sono: così la
         * riga di un file di soli enunciati resta quella di sempre. */
        if (report.solved) printf(", %d risolti", report.solved);
        printf(".\n");
        if (report.proved + report.solved != report.total) all_proved = 0;
    }
    if (unjustified_steps)
        printf("ATTENZIONE: %d passi di dimostrazione (formule rilette, o certificati respinti dal verificatore) "
               "non hanno superato il controllo indipendente e sono stati scartati\n", unjustified_steps);
    if (certificates) fclose(certificates);
    if (documented) {
        const char *problem = document_close(&document);
        if (problem) printf("ERRORE: %s\n", problem);
    }
    if (figure) pl_close(figure);
    return all_proved ? 0 : 1;
}
