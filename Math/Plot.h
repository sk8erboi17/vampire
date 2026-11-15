/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Plot.h
 * The plots, as a module of its own: the interface of Math/quaerens/plot.c.
 *
 * plot.c is a small matplotlib written in C: a figure, its panels, and on
 * each panel lines, straight lines, bands, markers, a legend, ticks and
 * titles; a figure becomes a page of a PDF written byte by byte. It uses the
 * C standard library and nothing else, and knows nothing of mathematics.
 *
 * In Quaerens the engine includes plot.c in its one translation unit. Here
 * plot.c is compiled apart (Math/Plot.c) and the engine sees only this
 * interface: the functions and the three opaque types it uses, and the
 * colours. What each function does is said where it is defined, in plot.c.
 *
 * Checklist: this header repeats declarations of plot.c. Math/Plot.c
 * includes both, so that a prototype that no longer agrees with its
 * definition does not compile, and asserts the colours one by one.
 */

#ifndef __Math_Plot__
#define __Math_Plot__

#ifdef __cplusplus
extern "C" {
#endif

/* Math/Plot.c has the types from plot.c itself, and wants only the prototypes checked. */
#ifndef QUAERENS_PLOT_TYPES_DEFINED
typedef enum { PL_BLACK, PL_GRAY, PL_BLUE, PL_ORANGE, PL_GREEN, PL_RED } PlColor;
typedef struct PlFigure PlFigure;
typedef struct PlAxes PlAxes;
typedef struct PlPdf PlPdf;
#endif

PlFigure *pl_figure(double width, double height);
void pl_suptitle(PlFigure *figure, const char *text);
PlAxes *pl_add_axes(PlFigure *figure, double weight);
void pl_set_title(PlAxes *axes, const char *text);
void pl_set_xlim(PlAxes *axes, double low, double high);
void pl_set_ylim(PlAxes *axes, double low, double high);
void pl_set_xticks(PlAxes *axes, const double *at, const char *const *label, int count);
void pl_set_yticks(PlAxes *axes, const double *at, const char *const *label, int count);
void pl_plot(PlAxes *axes, const double *x, const double *y, int count, PlColor color, double width, const char *label);
void pl_axhline(PlAxes *axes, double y, PlColor color, double width, int dashed);
void pl_axvline(PlAxes *axes, double x, PlColor color, double width, int dashed);
void pl_axvspan(PlAxes *axes, double low, double high, PlColor color);
void pl_marker(PlAxes *axes, double x, double y, PlColor color, int filled);
void pl_legend(PlAxes *axes);
void pl_close(PlFigure *figure);
PlPdf *pl_pdf_open(const char *path);
int pl_pdf_savefig(PlPdf *pdf, const PlFigure *figure);
int pl_pdf_close(PlPdf *pdf);

#ifdef __cplusplus
}
#endif

#endif /* __Math_Plot__ */
