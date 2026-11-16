/* INTERFACCIA DI output.c: il documento finale: enunciati, spiegazioni,
 * dimostrazioni, soluzioni e grafici in LaTeX, e la sua compilazione in PDF
 * (capitoli 41 e 22).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * output.c. Ciò che il modulo usa solo per sé non è qui: là è static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_OUTPUT_H
#define QUAERENS_OUTPUT_H

#include "engine_foundations.h"
#include "engine_induction.h"
#include "engine_explanation.h"

/* Il documento finale in corso di scrittura, con il PDF dei suoi grafici. */
typedef struct {
    FILE *tex;              /* il documento LaTeX, aperto in scrittura */
    char tex_path[1024];    /* il suo percorso */
    int want_pdf;           /* 1 se alla fine va compilato in PDF */
    PlPdf *plots;           /* il PDF dei grafici; NULL finché non ce n'è uno */
    char plots_path[1040];  /* il suo percorso: quello del documento, con
                               "-plots.pdf" al posto dell'estensione */
    int plots_pages;        /* pagine scritte finora nel PDF dei grafici */
    int plots_failed;       /* 1 se un grafico non si è potuto scrivere */
} Document;

const char *document_open(Document *document, const char *path);
void document_section(Document *document, const char *title);
void document_list(Document *document, int opening);
void document_item(Document *document, const char *formula, const Verdict *verdict, const PlFigure *plot, const Explanation *explanation);
const char *document_close(Document *document);

#endif /* QUAERENS_OUTPUT_H */
