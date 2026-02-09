#ifndef _kissat_h_INCLUDED
#define _kissat_h_INCLUDED

#include <stdint.h>

typedef struct kissat kissat;

// Default (partial) IPASIR interface.

const char *kissat_signature (void);
kissat *kissat_init (void);
void kissat_add (kissat *solver, int lit);
int kissat_solve (kissat *solver);
int kissat_value (kissat *solver, int lit);
void kissat_release (kissat *solver);

void kissat_set_terminate (kissat *solver, void *state,
                           int (*terminate) (void *state));

// Additional API functions.

void kissat_terminate (kissat *solver);
void kissat_reserve (kissat *solver, int max_var);

const char *kissat_id (void);
const char *kissat_version (void);
const char *kissat_compiler (void);

const char **kissat_copyright (void);
void kissat_build (const char *line_prefix);
void kissat_banner (const char *line_prefix, const char *name_of_app);

int kissat_get_option (kissat *solver, const char *name);
int kissat_set_option (kissat *solver, const char *name, int new_value);

void kissat_set_prefix (kissat *solver, const char *prefix);

int kissat_has_configuration (const char *name);
int kissat_set_configuration (kissat *solver, const char *name);

void kissat_set_conflict_limit (kissat *solver, unsigned);
void kissat_set_decision_limit (kissat *solver, unsigned);

void kissat_print_statistics (kissat *solver);
uint64_t kissat_get_solver_conflicts (kissat *solver);
uint64_t kissat_get_solver_learned (kissat *solver);
unsigned kissat_get_solver_active_variables (kissat *solver);
uint64_t kissat_get_solver_active_clauses (kissat *solver);
uint64_t kissat_get_solver_binary_clauses (kissat *solver);
uint64_t kissat_get_solver_irredundant_clauses (kissat *solver);
uint64_t kissat_get_solver_redundant_clauses (kissat *solver);
double kissat_get_remaining_clause_score (kissat *solver);
double kissat_get_remaining_unfitness (kissat *solver);
// Set initial phases from an external-variable indexed array.
// `phases[0]` corresponds to external variable 1.
// Values should be -1 or +1 (0 means "unset").
void kissat_set_initial_phases (kissat *solver, const int8_t *phases,
                                unsigned vars);

// Clause sharing between solver instances (portfolio / EA).
//
// `kissat_export_shared_clauses` iterates over shareable learned clauses
// and calls `consumer` for each clause. The literals are in external
// representation and only valid during the callback. Returning non-zero
// from `consumer` stops iteration.
// Limits are optional: `max_size`, `max_glue`, and `max_clauses` of zero
// mean "no limit".
//
// `kissat_import_shared_clause` adds a clause as redundant (learned).
// Importing shared clauses is not supported while proof logging is enabled.
// Returns 1 if the clause was used (added or propagated), 0 if skipped
// (tautology, satisfied, or trivial), and 2 if it created inconsistency.
typedef int (*kissat_shared_clause_consumer) (void *state, unsigned size,
                                              unsigned glue,
                                              const int *lits);

void kissat_export_shared_clauses (kissat *solver, unsigned max_size,
                                   unsigned max_glue, unsigned max_clauses,
                                   void *state,
                                   kissat_shared_clause_consumer consumer);

int kissat_import_shared_clause (kissat *solver, unsigned size,
                                 const int *lits, unsigned glue);

#endif
