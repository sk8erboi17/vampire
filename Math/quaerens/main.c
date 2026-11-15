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
 * Il programma è fatto di cinque file, e questo include gli altri quattro:
 *
 *   main.c     il motore: cerca, calcola, decide, ricontrolla;
 *   parser.c   la lettura del LaTeX: dal testo agli alberi;
 *   output.c   il documento finale, con dimostrazioni, soluzioni e grafici;
 *   plot.c     i grafici: un piccolo matplotlib in C, che scrive PDF;
 *   checker.c  il verificatore indipendente dei certificati.
 *
 * parser.c e output.c sono volumi di questo stesso libro: usano ciò che qui
 * viene prima della riga che li include. plot.c e checker.c sono programmi a
 * sé, che non sanno nulla degli altri, e di loro si usa solo l'interfaccia.
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
 * aritmetica e i suoi polinomi, non usa nulla di questo file, ed è abbastanza
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
 * COMPILAZIONE
 *
 *     cc -std=c11 -O2 -Wall -Wextra -o mathresearcher main.c
 *
 * Servono GCC o Clang: i conti esatti usano __int128. main.c include
 * parser.c, output.c, plot.c e checker.c, che devono stare nella stessa
 * cartella; il verificatore si compila anche da solo (vedi la testa di
 * checker.c). Per avere il documento finale in PDF serve inoltre un
 * compilatore LaTeX installato (tectonic oppure pdflatex); senza, il
 * programma scrive comunque il documento .tex e il PDF dei grafici.
 *
 * INDICE DEI CAPITOLI
 *
 * La numerazione è una sola per i tre file che formano il programma. I
 * capitoli segnati con un nome di file stanno in quel file, incluso da qui
 * nel punto in cui compaiono nell'elenco. Il capitolo 18, il più lungo, è
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

/* I VOLUMI DEL MOTORE (generato da Math/tools/engine_volumes.py: non modificare a mano)
 *
 * Il motore è un solo libro in più volumi, letti in quest'ordine in una sola
 * unità di compilazione: un capitolo usa ciò che i capitoli sopra di lui
 * hanno presentato, in questo volume o in quelli prima. I volumi uniti in
 * quest'ordine sono, byte per byte, il file unico da cui sono stati tagliati
 * (engine_volumes.py join lo riscrive, per confrontarlo con quello di Quaerens). */

/* limiti, errori e memoria, numeri esatti, monomi, polinomi, atomi, frazioni di polinomi (capitoli 1-7; include checker.c, plot.c e parser.c dove il libro ne ha bisogno) */
#include "engine_foundations.c"

/* le successioni note come dati, la valutazione di un albero in una frazione, i test di annullamento (capitoli 10-12) */
#include "engine_evaluation.c"

/* induzione su somme e prodotti: caso base, passo, verdetto (capitolo 13) */
#include "engine_induction.c"

/* relazioni tra insiemi: decisione per regioni, verifica indipendente, dimostrazione scritta (capitoli 15-16) */
#include "engine_sets.c"

/* i numeri reali come intervalli con l'errore garantito (capitolo 24) */
#include "engine_intervals.c"

/* enunciati con quantificatori sui numeri: le regole di dimostrazione (capitoli da 18 a 18.7) */
#include "engine_quantifiers.c"

/* la tabella dei segni: punti esatti, segni, righe, soluzioni, grafici, un parametro (capitoli 18.8-18.19) */
#include "engine_sign_tables.c"

/* la spiegazione: i passaggi registrati e ricontrollati (capitolo 40) */
#include "engine_explanation.c"

/* enunciati con quantificatori: verifica indipendente e verdetto (capitolo 19) */
#include "engine_quantifiers_verdict.c"

/* induzione su una disuguaglianza, successioni definite per ricorrenza (capitoli 25-26) */
#include "engine_sequences.c"

/* derivate: dimostrarle, calcolarle, usarle negli studi di funzione (capitolo 27) */
#include "engine_derivatives.c"

/* insiemi qualsiasi: modelli finiti, istanze, saturazione, e i compiti svolti per Vampire (capitolo 28) */
#include "engine_logic.c"

/* limiti (capitolo 29) */
#include "engine_limits.c"

/* integrali: primitive, integrali definiti e impropri (capitolo 30) */
#include "engine_integrals.c"

/* algebra lineare esatta: matrici, determinanti, sistemi lineari (capitoli 32-33) */
#include "engine_linear_algebra.c"

/* funzioni di più variabili: derivate parziali, gradiente, hessiana, punti critici (capitoli 35-36) */
#include "engine_multivariable.c"

/* identità con gli indici: il conto su tutti i valori (capitolo 38) */
#include "engine_indices.c"

/* dimostrare un enunciato: quale capitolo lo legge; il documento (include output.c); main (capitoli 20 e 23) */
#include "engine_statement.c"

/* Fine dei volumi. */
