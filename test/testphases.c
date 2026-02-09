#include "../src/kissat.h"

#include "test.h"

static void test_initial_phases_with_gaps (void) {
  kissat *solver = kissat_init ();
  tissat_init_solver (solver);
#ifndef NOPTIONS
  kissat_set_option (solver, "tumble", 1);
#endif
  kissat_reserve (solver, 100);
  kissat_add (solver, 100);
  kissat_add (solver, 0);

  int8_t phases[100];
  for (int i = 0; i < 100; i++)
    phases[i] = (i & 1) ? 1 : -1;

  kissat_set_initial_phases (solver, phases, 100);
  kissat_release (solver);
}

void tissat_schedule_phases (void) {
  SCHEDULE_FUNCTION (test_initial_phases_with_gaps);
}
