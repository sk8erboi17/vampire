/* INTERFACCIA DI engine_logic.c: insiemi qualsiasi: modelli finiti, istanze,
 * saturazione, e i compiti svolti per Vampire (capitolo 28).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_logic.c. Ciò che il modulo usa solo per sé non è qui: là è static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_LOGIC_H
#define QUAERENS_ENGINE_LOGIC_H

#include "engine_foundations.h"
#include "engine_induction.h"

/* DENTRO VAMPIRE: CHI FA CHE COSA SU UN ENUNCIATO DI LOGICA
 *
 * Questo file, dentro Vampire, è il motore matematico di un solo programma.
 * Su un enunciato su insiemi qualsiasi i due lavorano insieme, ciascuno
 * nella parte in cui è il migliore, e prove_abstract() non decide più da
 * sola: fa il compito che le viene chiesto in logic_task.
 *
 *   LOGIC_DECIDE       il capitolo com'è sempre stato: legge, cerca un
 *                      modello, cerca una dimostrazione. È ciò che fa il
 *                      programma da solo. Dentro Vampire è il primo turno
 *                      sugli enunciati con insiemi di parti o di
 *                      applicazioni, dove un modello deve avere TUTTE le
 *                      parti e TUTTE le applicazioni (28m) e una prova
 *                      deve saper scegliere le parti che le servono: lì
 *                      questo capitolo fa meglio di un dimostratore del
 *                      primo ordine (misurato: Math/README.md), e Vampire
 *                      interviene dopo, se qui non c'è risposta. Per ciò
 *                      che al primo ordine non si dice (quantificatori su
 *                      parti) Vampire interviene dopo sulle clausole del
 *                      verificatore (LOGIC_CLAUSES); per l'equipotenza
 *                      questo è il solo turno, perché dimostrarla vuol dire
 *                      costruire una biiezione.
 *   LOGIC_HAND_OVER    legge l'enunciato, svolge la notazione dei libri
 *                      (17q), ricontrolla lo svolgimento sui modelli finiti
 *                      (28h), e consegna l'enunciato svolto nella notazione
 *                      dei certificati: NOT_PROVED con reason ==
 *                      LOGIC_HANDED_OVER e l'enunciato in detail. Con
 *                      l'enunciato consegna le leggi delle parti e delle
 *                      applicazioni (28n), come voci axiom: sono vere in
 *                      ogni interpretazione ammessa, e chi dimostra ne ha
 *                      bisogno come delle ipotesi. La ricerca della
 *                      dimostrazione è di Vampire. Non si consegna un
 *                      enunciato che parla solo dei numeri che scrive
 *                      (28m): lì non c'è nulla da cercare, c'è un conto, e
 *                      il conto è di questo capitolo.
 *   LOGIC_ADOPT_MODEL  Vampire ha trovato un modello finito. Lo si carica
 *                      nella struttura dei modelli di questo capitolo
 *                      (model_adopt()) e da lì in poi è un modello come
 *                      quelli trovati qui: vi si ricalcolano ipotesi e
 *                      tesi, e l'enunciato com'è scritto (28h); lo si
 *                      scrive come controesempio e come certificato; lo
 *                      giudica checker.c. Un solo percorso per i modelli,
 *                      chiunque li abbia trovati.
 *   LOGIC_CERTIFY      Vampire ha dimostrato l'enunciato. Qui si scrive una
 *                      dimostrazione che checker.c sa ricontrollare: per
 *                      clausole (28u) o per istanze (28b-28g). La ricerca
 *                      dei modelli con il SAT non si fa: che l'enunciato
 *                      sia un teorema lo ha già stabilito Vampire, e qui
 *                      serve la prova, non il verdetto. Resta la ricerca
 *                      breve sui modelli piccoli (28a), che dà il controllo
 *                      indipendente alle prove per istanze; se trovasse un
 *                      controesempio, sarebbe la prova di Vampire a essere
 *                      sbagliata, e chi chiama lo deve dire.
 *
 *   LOGIC_CLAUSES      consegna le clausole da cui il verificatore fa
 *                      partire una prova per saturazione (11m di checker.c):
 *                      l'enunciato negato in forma normale, con i predicati
 *                      di dominio per gli insiemi forse vuoti, le funzioni di
 *                      Skolem e i nomi delle sottoformule, nella numerazione
 *                      che il verificatore ricostruisce da sé (sp_prepare()).
 *                      Vampire cerca la refutazione di QUELLE clausole, e
 *                      ogni sua inferenza diventa un passo che il
 *                      verificatore ricontrolla (Proof/Replay): così una
 *                      prova di Vampire è certificata per ciò che è, senza
 *                      che questo capitolo la rifaccia. Per un enunciato
 *                      che chiede un esempio ("esistono insiemi e simboli
 *                      per cui E") ciò che Vampire può dimostrare è che
 *                      l'esempio non c'è: l'enunciato del certificato è
 *                      allora "non E", e le clausole sono quelle di E.
 *                      Con i quantificatori su parti si consegnano anche le
 *                      istanze che si propongono senza cercare
 *                      (sp_static_comprehensions()): su queste clausole
 *                      Vampire può dimostrare ciò che questo capitolo non
 *                      ha dimostrato, e la prova è subito un certificato.
 *
 *   LOGIC_NUMBERS      non riguarda questo capitolo ma gli enunciati con
 *                      quantificatori sui numeri (capitoli 17 e 18): quelli
 *                      che il motore sa leggere e non decidere si consegnano
 *                      alle teorie aritmetiche di Vampire
 *                      (numbers_handed_over(), in fondo al file, dove
 *                      prove_core() smista gli enunciati).
 *
 * Così la ricerca è una sola (di Vampire), la certificazione è una sola (di
 * checker.c), e questo capitolo dà a ciascuna ciò che le serve: l'enunciato
 * letto bene, i modelli ricontrollati, le prove in una forma controllabile.
 *
 * Warning: è il solo capitolo che sa di essere ospitato. Se cambia la
 * notazione scritta da cert_abstract_head(), va aggiornato il lettore in
 * Math/LogicStatement.cpp; se cambia l'ordine delle tabelle di un modello,
 * model_adopt() e chi la chiama (Math/Engine.c). */
enum { LOGIC_DECIDE, LOGIC_HAND_OVER, LOGIC_ADOPT_MODEL, LOGIC_CERTIFY, LOGIC_CLAUSES, LOGIC_NUMBERS };

extern int logic_task;
extern const char *const LOGIC_HANDED_OVER;
extern const size_t *adopted_sizes;
extern const size_t *const *adopted_tables;
extern const size_t *adopted_cells;
extern int adopted_sorts, adopted_symbols;
Verdict prove_abstract(const char *formula);

#endif /* QUAERENS_ENGINE_LOGIC_H */
