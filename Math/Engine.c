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
 * @file Engine.c
 * The translation unit that holds the mathematical engine, and the
 * implementation of its C interface (Engine.h).
 *
 * The engine (Math/quaerens/) is written as one translation unit: main.c
 * includes parser.c, output.c, plot.c and checker.c, and nearly everything
 * in it is static. This file includes it whole and defines, below it, the
 * few functions the rest of Vampire calls. That is why the interface can
 * reach the engine's internals without the engine exporting them.
 *
 * The engine's own main() is renamed and never called: the command line of
 * this program is Vampire's.
 *
 * Checklist: the interface relies on these names of the engine: engine_init,
 * next_item, read_item, prove_item, prove, verdict_print, logic_task and
 * its values, LOGIC_HANDED_OVER, the adopted_* inputs of model_adopt(),
 * abstract_example, stack_origin, operation_symbols, relation_commands,
 * greek_letters,
 * unjustified_steps, figure, figures_wanted, explanation,
 * explanations_wanted and the document_* functions of output.c. If the
 * engine renames one, this file stops compiling, which is the intent.
 */

#define main quaerens_standalone_main
#include "quaerens/main.c"
#undef main

#include "Engine.h"

/* The verdict of the last statement decided, kept for qr_document_item():
 * the document wants the engine's own structure, with the pointers intact. */
static Verdict last_verdict;

/* The one-line form of the last verdict. The buffer grows as needed and is
 * reused; it belongs to this file. */
static char* line_text;
static size_t line_capacity;

/* The document being written, if any. */
static Document open_document;
static int document_is_open;

/* The stack guard of the engine measures from the address of a local of
 * engine_init(), "at the top of the program". Inside Vampire the engine is
 * entered from different depths, so every entry point measures from itself:
 * the budget of the engine (stack_budget) then counts what the engine uses,
 * not what Vampire had already used on the way in. */
#define ENTER_ENGINE() char entry_marker; stack_origin = (uintptr_t)(void*)&entry_marker
/* Checklist: every function of the interface that reaches the engine's
 * reader (read_item(), prove()) starts with ENTER_ENGINE(). */

void qr_init(void)
{
  engine_init();
}

int qr_next_item(const char** position, const char** item, const char** end)
{
  return next_item(position, item, end);
}

const char* qr_item_formula(const char* item, const char* end, const char** formula)
{
  ENTER_ENGINE();
  Item statement;
  const char* problem = read_item(item, end, &statement);
  if (!problem) *formula = statement.formula;
  return problem;
}

/* Writes the one-line form of verdict into line_text and returns it, or
 * NULL if there is no memory or no temporary file. It is the engine's own
 * verdict_print(), so the words are exactly the ones the engine uses. */
static const char* verdict_line(const Verdict* verdict)
{
  FILE* memory = tmpfile();
  if (!memory) return NULL;
  verdict_print(memory, verdict);
  long length = ftell(memory);
  rewind(memory);
  if (length < 0) { fclose(memory); return NULL; }
  if ((size_t)length + 1 > line_capacity) {
    char* grown = realloc(line_text, (size_t)length + 1);
    if (!grown) { fclose(memory); return NULL; }
    line_text = grown;
    line_capacity = (size_t)length + 1;
  }
  size_t read = fread(line_text, 1, (size_t)length, memory);
  line_text[read] = 0;
  fclose(memory);
  return line_text;
}

/* Turns the engine's verdict into the one of the interface. A verdict that
 * says "handed over" becomes QR_LOGIC with the statement in logic; if the
 * statement could not be written in the language of the certificates there
 * is nothing to hand over, and the caller is told so by a NULL logic. */
static QrVerdict export_verdict(const Verdict* verdict, int conditional, int remark)
{
  static const QrOutcome outcome[] = {
    [PROVED] = QR_PROVED, [REFUTED] = QR_REFUTED, [NOT_PROVED] = QR_NOT_PROVED,
    [UNSUPPORTED] = QR_UNSUPPORTED, [SOLVED] = QR_SOLVED
  };
  QrVerdict result = {0};
  last_verdict = *verdict;

  if (verdict->outcome == NOT_PROVED && verdict->reason == LOGIC_HANDED_OVER) {
    result.outcome = QR_LOGIC;
    result.logic = verdict->detail;
    result.wants_example = abstract_example;
    result.conditional = conditional;
    result.remark = remark;
    return result;
  }
  result.outcome = outcome[verdict->outcome];
  result.certified = verdict->certificate != NULL;
  result.line = verdict_line(verdict);
  result.method = verdict->method;
  result.reason = verdict->reason;
  result.detail = verdict->detail;
  result.note = verdict->note;
  result.proof = verdict->proof;
  result.certificate = verdict->certificate;
  result.induction_variable = verdict->variable;
  result.base = verdict->base;
  result.witness = verdict->witness;
  return result;
}

/* Decides the item with the engine's procedure for logic set to task (the
 * values of logic_task in Math/quaerens/main.c). The task matters only if
 * the statement is one of logic over arbitrary sets; it is put back to
 * "decide" at once, so that no later call inherits it. */
static QrVerdict decide_item(const char* item, const char* end, int task)
{
  ENTER_ENGINE();

  /* The flags of the text around the formula. prove_item() uses them to
   * hold back a counterexample when a condition was not read; for a
   * statement handed over, the caller needs them to do the same. */
  Item statement;
  int conditional = 0, remark = 0;
  if (!read_item(item, end, &statement)) { conditional = statement.conditional; remark = statement.remark; }

  logic_task = task;
  Verdict verdict = prove_item(item, end);
  logic_task = LOGIC_DECIDE;
  return export_verdict(&verdict, conditional, remark);
}

QrVerdict qr_decide_item(const char* item, const char* end, int delegate_logic)
{
  return decide_item(item, end, delegate_logic ? LOGIC_HAND_OVER : LOGIC_DECIDE);
}

QrVerdict qr_decide_formula(const char* formula, int delegate_logic)
{
  ENTER_ENGINE();
  logic_task = delegate_logic ? LOGIC_HAND_OVER : LOGIC_DECIDE;
  Verdict verdict = prove(formula, 'n', 0, 0);
  logic_task = LOGIC_DECIDE;
  return export_verdict(&verdict, 0, 0);
}

QrVerdict qr_adopt_model(const char* item, const char* end, const QrModel* model)
{
  adopted_sorts = (int)model->sorts;
  adopted_sizes = model->sizes;
  adopted_symbols = (int)model->symbols;
  adopted_tables = model->tables;
  adopted_cells = model->cells;

  /* A model that does not confirm is counted by the engine among its own
   * steps that failed a recheck. This one is not the engine's: whoever
   * found it answers for it, and the caller reports it. */
  int failed_before = unjustified_steps;
  QrVerdict verdict = decide_item(item, end, LOGIC_ADOPT_MODEL);
  unjustified_steps = failed_before;

  /* Borrowed for the call only. */
  adopted_sizes = NULL;
  adopted_tables = NULL;
  adopted_cells = NULL;
  adopted_sorts = adopted_symbols = 0;
  return verdict;
}

QrVerdict qr_certify_item(const char* item, const char* end)
{
  return decide_item(item, end, LOGIC_CERTIFY);
}

const char* const* qr_symbol_commands(QrCommands list, size_t* count)
{
  switch (list) {
    case QR_COMMANDS_OPERATIONS:
      *count = sizeof operation_symbols / sizeof *operation_symbols;
      return operation_symbols;
    case QR_COMMANDS_RELATIONS:
      *count = sizeof relation_commands / sizeof *relation_commands;
      return relation_commands;
    case QR_COMMANDS_GREEK:
      *count = sizeof greek_letters / sizeof *greek_letters;
      return greek_letters;
  }
  *count = 0;
  return NULL;
}

int qr_unjustified_steps(void)
{
  return unjustified_steps;
}

const char* qr_document_open(const char* path, int explanations)
{
  if (document_is_open) return "un documento è già aperto";
  const char* problem = document_open(&open_document, path);
  if (problem) return problem;

  /* Both signals are assigned, as the engine's own main() does: the plain
   * document must be plain even if explanations were asked for before. */
  document_is_open = figures_wanted = 1;
  explanations_wanted = explanations != 0;
  return NULL;
}

void qr_document_section(const char* title)
{
  if (document_is_open) document_section(&open_document, title);
}

void qr_document_list(int opening)
{
  if (document_is_open) document_list(&open_document, opening);
}

void qr_document_item(const char* item, const char* end)
{
  if (!document_is_open) return;
  ENTER_ENGINE();

  /* The statement goes in as it is written in the file: it is read again,
   * because the verdict does not carry it. This must come before the
   * verdict is used: read_item() does not touch the strings of a verdict. */
  Item statement;
  const char* unreadable = read_item(item, end, &statement);
  document_item(&open_document, unreadable ? NULL : statement.formula, &last_verdict, figure, &explanation);
}

void qr_document_external_item(const char* item, const char* end, QrOutcome outcome, const char* method,
                               const char* reason, const char* detail, const char* proof, const char* certificate)
{
  if (!document_is_open) return;
  ENTER_ENGINE();
  static const Outcome engine_outcome[] = {
    [QR_PROVED] = PROVED, [QR_REFUTED] = REFUTED, [QR_SOLVED] = SOLVED,
    [QR_NOT_PROVED] = NOT_PROVED, [QR_UNSUPPORTED] = UNSUPPORTED, [QR_LOGIC] = NOT_PROVED
  };
  Verdict verdict = {engine_outcome[outcome], 0, 0, 0, reason, detail, proof, method, NULL, certificate};

  /* No plot and no worked solution: those are records of the engine's own
   * computations, and this item was not computed by the engine. */
  Item statement;
  const char* unreadable = read_item(item, end, &statement);
  document_item(&open_document, unreadable ? NULL : statement.formula, &verdict, NULL, NULL);
}

const char* qr_document_close(void)
{
  if (!document_is_open) return NULL;
  document_is_open = 0;
  const char* problem = document_close(&open_document);
  if (figure) { pl_close(figure); figure = NULL; }
  return problem;
}
