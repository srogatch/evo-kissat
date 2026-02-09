#include "../src/clause.h"
#include "../src/kissat.h"

#include "test.h"

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

void tissat_schedule_fitness (void) {
  SCHEDULE_FUNCTION (test_remaining_clause_score_with_invalid_lit);
}
