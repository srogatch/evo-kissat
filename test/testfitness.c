#include "../src/clause.h"
#include "../src/kissat.h"

#include "test.h"

#include <math.h>

static void test_remaining_clause_score_with_invalid_lit (void) {
  kissat *solver = kissat_init ();
  tissat_init_solver (solver);
  kissat_reserve (solver, 3);
  kissat_add (solver, 1);
  kissat_add (solver, 2);
  kissat_add (solver, 3);
  kissat_add (solver, 0);

  clause *c = kissat_last_irredundant_clause (solver);
  assert (c);
  assert (c->size == 3);
  c->lits[1] = INVALID_LIT;

  double score = kissat_get_remaining_clause_score (solver);
  assert (score > 0.0);

  kissat_release (solver);
}

static void test_remaining_unfitness_formula (void) {
  kissat *solver = kissat_init ();
  tissat_init_solver (solver);
  kissat_reserve (solver, 4);

  kissat_add (solver, 1);
  kissat_add (solver, 2);
  kissat_add (solver, 3);
  kissat_add (solver, 0);

  kissat_add (solver, 1);
  kissat_add (solver, -2);
  kissat_add (solver, 0);

  kissat_add (solver, -1);
  kissat_add (solver, 3);
  kissat_add (solver, 4);
  kissat_add (solver, 2);
  kissat_add (solver, 0);

  kissat_add (solver, 1);
  kissat_add (solver, -3);
  kissat_add (solver, 4);
  kissat_add (solver, 0);
  // Add a 3-literal redundant clause and ensure it does not affect the
  // irredundant-clause component used in unfitness.
  const int redundant_clause[3] = {1, 2, 4};
  const int imported =
      kissat_import_shared_clause (solver, 3, redundant_clause, 1);
  if (imported != 1)
    FATAL ("expected redundant shared clause to be imported, got %d", imported);

  const double expected =
      (4.0 - 0.5 * sqrt (1.0)) / log2 (3.0 + 2.0);
  const double got = kissat_get_remaining_unfitness (solver);
  if (fabs (got - expected) > 1e-9)
    FATAL ("expected unfitness %.17g, got %.17g", expected, got);

  kissat_release (solver);
}

void tissat_schedule_fitness (void) {
  SCHEDULE_FUNCTION (test_remaining_clause_score_with_invalid_lit);
  SCHEDULE_FUNCTION (test_remaining_unfitness_formula);
}
