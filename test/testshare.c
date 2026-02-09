#include "../src/kissat.h"

#include "test.h"

typedef struct share_expect share_expect;

struct share_expect {
  unsigned size;
  unsigned glue;
  int lits[4];
  unsigned seen;
};

static int match_shared_clause (void *state, unsigned size, unsigned glue,
                                const int *lits) {
  share_expect *expect = state;
  if (size != expect->size)
    return 0;
  if (glue != expect->glue)
    return 0;
  for (unsigned i = 0; i < size; i++)
    if (lits[i] != expect->lits[i])
      return 0;
  expect->seen++;
  return 1;
}

static void test_share_export_ternary (void) {
  kissat *solver = kissat_init ();
  const int clause[3] = {1, -2, 3};
  const int res = kissat_import_shared_clause (solver, 3, clause, 2);
  assert (res == 1);
  share_expect expect;
  memset (&expect, 0, sizeof expect);
  expect.size = 3;
  expect.glue = 2;
  expect.lits[0] = clause[0];
  expect.lits[1] = clause[1];
  expect.lits[2] = clause[2];
  kissat_export_shared_clauses (solver, 3, 3, 0, &expect,
                                match_shared_clause);
  assert (expect.seen == 1);
  kissat_release (solver);
}

static void test_share_export_binary (void) {
  kissat *solver = kissat_init ();
  int clause[2] = {1, -2};
  const int res = kissat_import_shared_clause (solver, 2, clause, 4);
  assert (res == 1);
  if (clause[0] > clause[1]) {
    const int tmp = clause[0];
    clause[0] = clause[1];
    clause[1] = tmp;
  }
  share_expect expect;
  memset (&expect, 0, sizeof expect);
  expect.size = 2;
  expect.glue = 1;
  expect.lits[0] = clause[0];
  expect.lits[1] = clause[1];
  kissat_export_shared_clauses (solver, 2, 0, 0, &expect,
                                match_shared_clause);
  assert (expect.seen == 1);
  kissat_release (solver);
}

static void test_share_import_edgecases (void) {
  kissat *solver = kissat_init ();
  int res = kissat_import_shared_clause (solver, 0, 0, 0);
  assert (res == 2);
  assert (solver->inconsistent);
  kissat_release (solver);

  solver = kissat_init ();
  const int tautology[2] = {1, -1};
  res = kissat_import_shared_clause (solver, 2, tautology, 1);
  assert (res == 0);
  kissat_release (solver);

  solver = kissat_init ();
  kissat_add (solver, 1);
  kissat_add (solver, 0);
  const int satisfied[2] = {1, 2};
  res = kissat_import_shared_clause (solver, 2, satisfied, 1);
  assert (res == 0);
  kissat_release (solver);
}

void tissat_schedule_share (void) {
  SCHEDULE_FUNCTION (test_share_export_ternary);
  SCHEDULE_FUNCTION (test_share_export_binary);
  SCHEDULE_FUNCTION (test_share_import_edgecases);
}
