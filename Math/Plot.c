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
 * @file Plot.c
 * The translation unit of the plots (Plot.h).
 *
 * plot.c is included whole and nothing else of the program is: its
 * interface functions have external linkage already, its helpers are
 * static, and the mathematical engine, which is compiled apart, reaches it
 * only through Plot.h.
 */

#include "quaerens/plot.c"

/* The interface as the engine sees it, checked against the definitions
 * above: a prototype that differs does not compile. The types are those
 * of plot.c itself. */
#define QUAERENS_PLOT_TYPES_DEFINED
#include "Plot.h"

/* The colours are repeated in Plot.h: if plot.c gains one, or changes their
 * order, the header must follow. */
_Static_assert(PL_BLACK == 0 && PL_GRAY == 1 && PL_BLUE == 2 && PL_ORANGE == 3 && PL_GREEN == 4 && PL_RED == 5 && PL_COLORS == 6,
               "the colours of Math/Plot.h are not those of plot.c");
