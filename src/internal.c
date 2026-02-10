#include "allocate.h"
#include "backtrack.h"
#include "error.h"
#include "import.h"
#include "inline.h"
#include "inlineframes.h"
#include "print.h"
#include "propsearch.h"
#include "require.h"
#include "resize.h"
#include "resources.h"
#include "search.h"

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

void kissat_reset_last_learned (kissat *solver) {
  for (really_all_last_learned (p))
    *p = INVALID_REF;
}

kissat *kissat_init (void) {
  kissat *solver = kissat_calloc (0, 1, sizeof *solver);
#ifndef NOPTIONS
  kissat_init_options (&solver->options);
#else
  kissat_init_options ();
#endif
#ifndef QUIET
  kissat_init_profiles (&solver->profiles);
#endif
  START (total);
  kissat_init_queue (solver);
  assert (INTERNAL_MAX_LIT < UINT_MAX);
  kissat_push_frame (solver, UINT_MAX);
  solver->watching = true;
  solver->conflict.size = 2;
  solver->scinc = 1.0;
  solver->first_reducible = INVALID_REF;
  solver->last_irredundant = INVALID_REF;
  kissat_reset_last_learned (solver);
#ifndef NDEBUG
  kissat_init_checker (solver);
#endif
  solver->prefix = kissat_strdup (solver, "c ");
  return solver;
}

void kissat_set_prefix (kissat *solver, const char *prefix) {
  kissat_freestr (solver, solver->prefix);
  solver->prefix = kissat_strdup (solver, prefix);
}

#define DEALLOC_GENERIC(NAME, ELEMENTS_PER_BLOCK) \
  do { \
    const size_t block_size = ELEMENTS_PER_BLOCK * sizeof *solver->NAME; \
    kissat_dealloc (solver, solver->NAME, solver->size, block_size); \
    solver->NAME = 0; \
  } while (0)

#define DEALLOC_VARIABLE_INDEXED(NAME) DEALLOC_GENERIC (NAME, 1)

#define DEALLOC_LITERAL_INDEXED(NAME) DEALLOC_GENERIC (NAME, 2)

#define RELEASE_LITERAL_INDEXED_STACKS(NAME, ACCESS) \
  do { \
    for (all_stack (unsigned, IDX_RILIS, solver->active)) { \
      const unsigned LIT_RILIS = LIT (IDX_RILIS); \
      const unsigned NOT_LIT_RILIS = NOT (LIT_RILIS); \
      RELEASE_STACK (ACCESS (LIT_RILIS)); \
      RELEASE_STACK (ACCESS (NOT_LIT_RILIS)); \
    } \
    DEALLOC_LITERAL_INDEXED (NAME); \
  } while (0)

void kissat_release (kissat *solver) {
  kissat_require_initialized (solver);
  kissat_release_heap (solver, SCORES);
  kissat_release_heap (solver, &solver->schedule);
  kissat_release_vectors (solver);
  kissat_release_phases (solver);

  RELEASE_STACK (solver->export);
  RELEASE_STACK (solver->import);

  DEALLOC_VARIABLE_INDEXED (assigned);
  DEALLOC_VARIABLE_INDEXED (flags);
  DEALLOC_VARIABLE_INDEXED (links);

  DEALLOC_LITERAL_INDEXED (marks);
  DEALLOC_LITERAL_INDEXED (values);
  DEALLOC_LITERAL_INDEXED (watches);

  RELEASE_STACK (solver->import);
  RELEASE_STACK (solver->eliminated);
  RELEASE_STACK (solver->extend);
  RELEASE_STACK (solver->witness);
  RELEASE_STACK (solver->etrail);

  RELEASE_STACK (solver->delayed);

  RELEASE_STACK (solver->clause);
  RELEASE_STACK (solver->shadow);
#if defined(LOGGING) || !defined(NDEBUG)
  RELEASE_STACK (solver->resolvent);
#endif

  RELEASE_STACK (solver->arena);

  RELEASE_STACK (solver->units);
  RELEASE_STACK (solver->shared_binaries);
  RELEASE_STACK (solver->frames);
  RELEASE_STACK (solver->sorter);

  RELEASE_ARRAY (solver->trail, solver->size);

  RELEASE_STACK (solver->analyzed);
  RELEASE_STACK (solver->levels);
  RELEASE_STACK (solver->minimize);
  RELEASE_STACK (solver->poisoned);
  RELEASE_STACK (solver->promote);
  RELEASE_STACK (solver->removable);
  RELEASE_STACK (solver->shrinkable);
  RELEASE_STACK (solver->xorted[0]);
  RELEASE_STACK (solver->xorted[1]);

  RELEASE_STACK (solver->sweep_schedule);

  RELEASE_STACK (solver->ranks);

  RELEASE_STACK (solver->antecedents[0]);
  RELEASE_STACK (solver->antecedents[1]);
  RELEASE_STACK (solver->gates[0]);
  RELEASE_STACK (solver->gates[1]);
  RELEASE_STACK (solver->resolvents);

#if !defined(NDEBUG) || !defined(NPROOFS)
  RELEASE_STACK (solver->added);
  RELEASE_STACK (solver->removed);
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
  RELEASE_STACK (solver->original);
#endif

#ifndef QUIET
  RELEASE_STACK (solver->profiles.stack);
#endif

  kissat_freestr (solver, solver->prefix);

#ifndef NDEBUG
  kissat_release_checker (solver);
#endif
#if !defined(NDEBUG) && defined(METRICS)
  uint64_t leaked = solver->statistics.allocated_current;
  if (leaked)
    if (!getenv ("LEAK"))
      kissat_fatal ("internally leaking %" PRIu64 " bytes", leaked);
#endif

  kissat_free (0, solver, sizeof *solver);
}

void kissat_reserve (kissat *solver, int max_var) {
  kissat_require_initialized (solver);
  kissat_require (0 <= max_var, "negative maximum variable argument '%d'",
                  max_var);
  kissat_require (max_var <= EXTERNAL_MAX_VAR,
                  "invalid maximum variable argument '%d'", max_var);
  kissat_increase_size (solver, (unsigned) max_var);
  if (!GET_OPTION (tumble)) {
    for (int idx = 1; idx <= max_var; idx++)
      (void) kissat_import_literal (solver, idx);
    for (unsigned idx = 0; idx != (unsigned) max_var; idx++)
      kissat_activate_literal (solver, LIT (idx));
  }
}

int kissat_get_option (kissat *solver, const char *name) {
  kissat_require_initialized (solver);
  kissat_require (name, "name zero pointer");
#ifndef NOPTIONS
  return kissat_options_get (&solver->options, name);
#else
  (void) solver;
  return kissat_options_get (name);
#endif
}

int kissat_set_option (kissat *solver, const char *name, int new_value) {
#ifndef NOPTIONS
  kissat_require_initialized (solver);
  kissat_require (name, "name zero pointer");
#ifndef NOPTIONS
  return kissat_options_set (&solver->options, name, new_value);
#else
  return kissat_options_set (name, new_value);
#endif
#else
  (void) solver, (void) new_value;
  return kissat_options_get (name);
#endif
}

void kissat_set_decision_limit (kissat *solver, unsigned limit) {
  kissat_require_initialized (solver);
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  statistics *statistics = &solver->statistics;
  limited->decisions = true;
  assert (UINT64_MAX - limit >= statistics->decisions);
  limits->decisions = statistics->decisions + limit;
  LOG ("set decision limit to %" PRIu64 " after %u decisions",
       limits->decisions, limit);
}

void kissat_set_conflict_limit (kissat *solver, unsigned limit) {
  kissat_require_initialized (solver);
  limits *limits = &solver->limits;
  limited *limited = &solver->limited;
  statistics *statistics = &solver->statistics;
  limited->conflicts = true;
  assert (UINT64_MAX - limit >= statistics->conflicts);
  limits->conflicts = statistics->conflicts + limit;
  LOG ("set conflict limit to %" PRIu64 " after %u conflicts",
       limits->conflicts, limit);
}

void kissat_print_statistics (kissat *solver) {
#ifndef QUIET
  kissat_require_initialized (solver);
  const int verbosity = kissat_verbosity (solver);
  if (verbosity < 0)
    return;
  if (GET_OPTION (profile)) {
    kissat_section (solver, "profiling");
    kissat_profiles_print (solver);
  }
  const bool complete = GET_OPTION (statistics);
  kissat_section (solver, "statistics");
  const bool verbose = (complete || verbosity > 0);
  kissat_statistics_print (solver, verbose);
#ifndef NPROOFS
  if (solver->proof) {
    kissat_section (solver, "proof");
    kissat_print_proof_statistics (solver, verbose);
  }
#endif
#ifndef NDEBUG
  if (GET_OPTION (check) > 1) {
    kissat_section (solver, "checker");
    kissat_print_checker_statistics (solver, verbose);
  }
#endif
  kissat_section (solver, "glue usage");
  kissat_print_glue_usage (solver);
  kissat_section (solver, "resources");
  kissat_print_resources (solver);
#endif
  (void) solver;
}

uint64_t kissat_get_solver_conflicts (kissat *solver) {
  kissat_require_initialized (solver);
  return solver->statistics.conflicts;
}

uint64_t kissat_get_solver_learned (kissat *solver) {
  kissat_require_initialized (solver);
  return solver->statistics.clauses_learned;
}

unsigned kissat_get_solver_active_variables (kissat *solver) {
  kissat_require_initialized (solver);
  return solver->active;
}

uint64_t kissat_get_solver_active_clauses (kissat *solver) {
  kissat_require_initialized (solver);
  return solver->statistics.clauses_irredundant +
         solver->statistics.clauses_redundant +
         solver->statistics.clauses_binary;
}

uint64_t kissat_get_solver_binary_clauses (kissat *solver) {
  kissat_require_initialized (solver);
  return solver->statistics.clauses_binary;
}

uint64_t kissat_get_solver_irredundant_clauses (kissat *solver) {
  kissat_require_initialized (solver);
  return solver->statistics.clauses_irredundant;
}

uint64_t kissat_get_solver_redundant_clauses (kissat *solver) {
  kissat_require_initialized (solver);
  return solver->statistics.clauses_redundant;
}

double kissat_get_remaining_clause_score (kissat *solver) {
  kissat_require_initialized (solver);
  value *values = solver->values;
  double sum = 0.0;

  for (all_clauses (c)) {
    if (c->garbage)
      continue;
    bool satisfied = false;
    unsigned remaining = 0;
    for (all_literals_in_clause (lit, c)) {
      if (lit == INVALID_LIT || lit >= LITS)
        continue;
      value v = values[lit];
      if (v > 0) {
        satisfied = true;
        break;
      }
      if (!v)
        remaining++;
    }
    if (satisfied)
      continue;
    if (!remaining)
      return -1e30;
    if (remaining < 63) {
      const double denom = (double) ((1ULL << remaining) - 1ULL);
      sum += 1.0 / denom;
    }
  }

  double binary_sum = 0.0;
  if (solver->watching) {
    for (all_literals (lit)) {
      watches *watches = &WATCHES (lit);
      for (all_binary_blocking_watches (watch, *watches)) {
        if (!watch.type.binary)
          continue;
        const unsigned other = watch.binary.lit;
        if (other == INVALID_LIT || other >= LITS)
          continue;
        const value v1 = values[lit];
        const value v2 = values[other];
        if (v1 > 0 || v2 > 0)
          continue;
        const unsigned remaining = (!v1) + (!v2);
        if (!remaining)
          return -1e30;
        if (remaining < 63) {
          const double denom = (double) ((1ULL << remaining) - 1ULL);
          binary_sum += 1.0 / denom;
        }
      }
    }
  } else {
    for (all_literals (lit)) {
      watches *watches = &WATCHES (lit);
      for (all_binary_large_watches (watch, *watches)) {
        if (!watch.type.binary)
          continue;
        const unsigned other = watch.binary.lit;
        if (other == INVALID_LIT || other >= LITS)
          continue;
        const value v1 = values[lit];
        const value v2 = values[other];
        if (v1 > 0 || v2 > 0)
          continue;
        const unsigned remaining = (!v1) + (!v2);
        if (!remaining)
          return -1e30;
        if (remaining < 63) {
          const double denom = (double) ((1ULL << remaining) - 1ULL);
          binary_sum += 1.0 / denom;
        }
      }
    }
  }

  sum += 0.5 * binary_sum;
  return sum;
}

double kissat_get_remaining_unfitness (kissat *solver) {
  kissat_require_initialized (solver);
  const double n_rem_vars = (double) solver->active;
  const double n_binary_clauses_plus_one =
      (double) solver->statistics.clauses_binary + 1.0;
  const double n_irredundant_clauses_plus_one =
      (double) solver->statistics.clauses_irredundant + 1.0;

  // Unfitness formula:
  // nRemVars - log2(nBinary + 1) + log2(nIrredundant + 1)
  return n_rem_vars - log2 (n_binary_clauses_plus_one) +
         log2 (n_irredundant_clauses_plus_one);
}

static bool shareable_external_literal (kissat *solver, int elit) {
  if (!elit)
    return false;
  const unsigned eidx = ABS (elit);
  if (eidx >= SIZE_STACK (solver->import))
    return false;
  const import *const imported = &PEEK_STACK (solver->import, eidx);
  // Extension variables are solver-local (their external ids can differ
  // across instances), so exporting clauses that contain them is unsound.
  return imported->imported && !imported->eliminated && !imported->extension;
}

void kissat_set_initial_phases (kissat *solver, const int8_t *phases,
                                unsigned vars) {
  kissat_require_initialized (solver);
  kissat_require (phases, "phases zero pointer");
  const size_t imported = SIZE_STACK (solver->import);
  if (!imported || !vars)
    return;
  unsigned limit = vars;
  if (limit + 1 > imported)
    limit = (unsigned) imported - 1;
  for (unsigned eidx = 1; eidx <= limit; eidx++) {
    const struct import *import = &PEEK_STACK (solver->import, eidx);
    if (!import->imported || import->eliminated)
      continue;
    const unsigned ilit = import->lit;
    const unsigned iidx = ilit / 2;
    int8_t v = phases[eidx - 1];
    if (v > 0)
      v = 1;
    else if (v < 0)
      v = -1;
    else
      v = 0;
    solver->phases.saved[iidx] = (value) v;
    solver->phases.target[iidx] = (value) v;
    solver->phases.best[iidx] = (value) v;
  }
}

void kissat_add (kissat *solver, int elit) {
  kissat_require_initialized (solver);
  kissat_require (!GET (searches), "incremental solving not supported");
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
  const int checking = kissat_checking (solver);
  const bool logging = kissat_logging (solver);
  const bool proving = kissat_proving (solver);
#endif
  if (elit) {
    kissat_require_valid_external_internal (elit);
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
    if (checking || logging || proving)
      PUSH_STACK (solver->original, elit);
#endif
    unsigned ilit = kissat_import_literal (solver, elit);

    const mark mark = MARK (ilit);
    if (!mark) {
      const value value = kissat_fixed (solver, ilit);
      if (value > 0) {
        if (!solver->clause_satisfied) {
          LOG ("adding root level satisfied literal %u(%d)@0=1", ilit,
               elit);
          solver->clause_satisfied = true;
        }
      } else if (value < 0) {
        LOG ("adding root level falsified literal %u(%d)@0=-1", ilit, elit);
        if (!solver->clause_shrink) {
          solver->clause_shrink = true;
          LOG ("thus original clause needs shrinking");
        }
      } else {
        MARK (ilit) = 1;
        MARK (NOT (ilit)) = -1;
        assert (SIZE_STACK (solver->clause) < UINT_MAX);
        PUSH_STACK (solver->clause, ilit);
      }
    } else if (mark < 0) {
      assert (mark < 0);
      if (!solver->clause_trivial) {
        LOG ("adding dual literal %u(%d) and %u(%d)", NOT (ilit), -elit,
             ilit, elit);
        solver->clause_trivial = true;
      }
    } else {
      assert (mark > 0);
      LOG ("adding duplicated literal %u(%d)", ilit, elit);
      if (!solver->clause_shrink) {
        solver->clause_shrink = true;
        LOG ("thus original clause needs shrinking");
      }
    }
  } else {
#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
    const size_t offset = solver->offset_of_last_original_clause;
    size_t esize = SIZE_STACK (solver->original) - offset;
    int *elits = BEGIN_STACK (solver->original) + offset;
    assert (esize <= UINT_MAX);
#endif
    ADD_UNCHECKED_EXTERNAL (esize, elits);
    const size_t isize = SIZE_STACK (solver->clause);
    unsigned *ilits = BEGIN_STACK (solver->clause);
    assert (isize < (unsigned) INT_MAX);

    if (solver->inconsistent)
      LOG ("inconsistent thus skipping original clause");
    else if (solver->clause_satisfied)
      LOG ("skipping satisfied original clause");
    else if (solver->clause_trivial)
      LOG ("skipping trivial original clause");
    else {
      kissat_activate_literals (solver, isize, ilits);

      if (!isize) {
        if (solver->clause_shrink)
          LOG ("all original clause literals root level falsified");
        else
          LOG ("found empty original clause");

        if (!solver->inconsistent) {
          LOG ("thus solver becomes inconsistent");
          solver->inconsistent = true;
          CHECK_AND_ADD_EMPTY ();
          ADD_EMPTY_TO_PROOF ();
        }
      } else if (isize == 1) {
        unsigned unit = TOP_STACK (solver->clause);

        if (solver->clause_shrink)
          LOGUNARY (unit, "original clause shrinks to");
        else
          LOGUNARY (unit, "found original");

        kissat_original_unit (solver, unit);

        COVER (solver->level);
        if (!solver->level)
          (void) kissat_search_propagate (solver);
      } else {
        reference res = kissat_new_original_clause (solver);

        const unsigned a = ilits[0];
        const unsigned b = ilits[1];

        const value u = VALUE (a);
        const value v = VALUE (b);

        const unsigned k = u ? LEVEL (a) : UINT_MAX;
        const unsigned l = v ? LEVEL (b) : UINT_MAX;

        bool assign = false;

        if (!u && v < 0) {
          LOG ("original clause immediately forcing");
          assign = true;
        } else if (u < 0 && k == l) {
          LOG ("both watches falsified at level @%u", k);
          assert (v < 0);
          assert (k > 0);
          kissat_backtrack_without_updating_phases (solver, k - 1);
        } else if (u < 0) {
          LOG ("watches falsified at levels @%u and @%u", k, l);
          assert (v < 0);
          assert (k > l);
          assert (l > 0);
          assign = true;
        } else if (u > 0 && v < 0) {
          LOG ("first watch satisfied at level @%u "
               "second falsified at level @%u",
               k, l);
          assert (k <= l);
        } else if (!u && v > 0) {
          LOG ("first watch unassigned "
               "second falsified at level @%u",
               l);
          assign = true;
        } else {
          assert (!u);
          assert (!v);
        }

        if (assign) {
          assert (solver->level > 0);

          if (isize == 2) {
            assert (res == INVALID_REF);
            kissat_assign_binary (solver, a, b);
          } else {
            assert (res != INVALID_REF);
            clause *c = kissat_dereference_clause (solver, res);
            kissat_assign_reference (solver, a, res, c);
          }
        }
      }
    }

#if !defined(NDEBUG) || !defined(NPROOFS)
    if (solver->clause_satisfied || solver->clause_trivial) {
#ifndef NDEBUG
      if (checking > 1)
        kissat_remove_checker_external (solver, esize, elits);
#endif
#ifndef NPROOFS
      if (proving) {
        if (esize == 1)
          LOG ("skipping deleting unit from proof");
        else
          kissat_delete_external_from_proof (solver, esize, elits);
      }
#endif
    } else if (!solver->inconsistent && solver->clause_shrink) {
#ifndef NDEBUG
      if (checking > 1) {
        kissat_check_and_add_internal (solver, isize, ilits);
        kissat_remove_checker_external (solver, esize, elits);
      }
#endif
#ifndef NPROOFS
      if (proving) {
        kissat_add_lits_to_proof (solver, isize, ilits);
        kissat_delete_external_from_proof (solver, esize, elits);
      }
#endif
    }
#endif

#if !defined(NDEBUG) || !defined(NPROOFS) || defined(LOGGING)
    if (checking) {
      LOGINTS (esize, elits, "saved original");
      PUSH_STACK (solver->original, 0);
      solver->offset_of_last_original_clause =
          SIZE_STACK (solver->original);
    } else if (logging || proving) {
      LOGINTS (esize, elits, "reset original");
      CLEAR_STACK (solver->original);
      solver->offset_of_last_original_clause = 0;
    }
#endif
    for (all_stack (unsigned, lit, solver->clause))
      MARK (lit) = MARK (NOT (lit)) = 0;

    CLEAR_STACK (solver->clause);

    solver->clause_satisfied = false;
    solver->clause_trivial = false;
    solver->clause_shrink = false;
  }
}

void kissat_export_shared_clauses (kissat *solver, unsigned max_size,
                                   unsigned max_glue, unsigned max_clauses,
                                   void *state,
                                   kissat_shared_clause_consumer consumer) {
  kissat_require_initialized (solver);
  kissat_require (consumer, "consumer zero pointer");

  size_t exported = 0;
  int *buffer = 0;
  size_t capacity = 0;

  for (all_stack (int, unit, solver->units)) {
    const int lit = unit;
    if (!shareable_external_literal (solver, lit))
      continue;
    if (consumer (state, 1, 1, &lit))
      goto DONE;
  }

  {
    const int *p = BEGIN_STACK (solver->shared_binaries);
    const int *const end = END_STACK (solver->shared_binaries);
    for (; p + 1 < end; p += 2) {
      if (!shareable_external_literal (solver, p[0]) ||
          !shareable_external_literal (solver, p[1]))
        continue;
      const int pair[2] = {p[0], p[1]};
      if (consumer (state, 2, 1, pair))
        goto DONE;
    }
  }

  for (all_clauses (c)) {
    if (max_clauses && exported >= max_clauses)
      break;
    if (c->garbage || !c->redundant)
      continue;
    if (max_size && c->size > max_size)
      continue;
    if (max_glue && c->glue > max_glue)
      continue;

    if (c->size > capacity) {
      const size_t old_bytes = capacity * sizeof *buffer;
      capacity = c->size;
      const size_t new_bytes = capacity * sizeof *buffer;
      buffer = kissat_realloc (solver, buffer, old_bytes, new_bytes);
    }

    bool ok = true;
    unsigned i = 0;
    for (all_literals_in_clause (lit, c)) {
      int elit = kissat_export_literal (solver, lit);
      if (!shareable_external_literal (solver, elit)) {
        ok = false;
        break;
      }
      buffer[i++] = elit;
    }
    if (!ok)
      continue;
    if (consumer (state, c->size, c->glue, buffer))
      break;
    exported++;
  }

DONE:
  if (buffer)
    kissat_free (solver, buffer, capacity * sizeof *buffer);
}

int kissat_import_shared_clause (kissat *solver, unsigned size,
                                 const int *lits, unsigned glue) {
  kissat_require_initialized (solver);
  kissat_require (!GET (searches), "incremental solving not supported");
#ifndef NPROOFS
  kissat_require (!kissat_proving (solver),
                  "can not import shared clauses while proving");
#endif
  kissat_require (EMPTY_STACK (solver->clause),
                  "incomplete clause (terminating zero not added)");
  kissat_require (lits || !size, "literal array zero pointer");

  int res = 0;
#if !defined(NDEBUG) && !defined(NOPTIONS)
  int restore_check = -1;
  if (GET_OPTION (check) > 1) {
    // Shared clauses from another solver are not guaranteed to be RUP in this
    // solver's current checker state. Disable strict checker insertion while
    // importing and register imported clauses explicitly as unchecked.
    restore_check = GET_OPTION (check);
    (void) kissat_set_option (solver, "check", 1);
  }
#else
  const int restore_check = -1;
#endif

  if (!size) {
#ifndef NDEBUG
    if (restore_check > 1)
      kissat_add_unchecked_external (solver, 0, 0);
#endif
    if (!solver->inconsistent) {
      solver->inconsistent = true;
      CHECK_AND_ADD_EMPTY ();
      ADD_EMPTY_TO_PROOF ();
    }
    res = 2;
    goto DONE;
  }

  solver->clause_satisfied = false;
  solver->clause_trivial = false;
  solver->clause_shrink = false;
  bool unmappable = false;

  for (unsigned i = 0; i < size; i++) {
    const int elit = lits[i];
    kissat_require (elit, "zero literal in shared clause");
    kissat_require_valid_external_internal (elit);
    unsigned ilit = kissat_import_literal (solver, elit);
    if (ilit == INVALID_LIT) {
      // Clause contains a variable eliminated in this solver instance.
      // Skip importing it into this instance.
      unmappable = true;
      break;
    }

    const mark mark = MARK (ilit);
    if (!mark) {
      const value value = kissat_fixed (solver, ilit);
      if (value > 0) {
        solver->clause_satisfied = true;
      } else if (value < 0) {
        solver->clause_shrink = true;
      } else {
        MARK (ilit) = 1;
        MARK (NOT (ilit)) = -1;
        assert (SIZE_STACK (solver->clause) < UINT_MAX);
        PUSH_STACK (solver->clause, ilit);
      }
    } else if (mark < 0) {
      solver->clause_trivial = true;
    } else {
      solver->clause_shrink = true;
    }
  }

  const size_t isize = SIZE_STACK (solver->clause);
  unsigned *ilits = BEGIN_STACK (solver->clause);

  if (solver->inconsistent) {
    res = 2;
  } else if (unmappable) {
    res = 0;
  } else if (solver->clause_satisfied || solver->clause_trivial) {
    res = 0;
  } else {
    kissat_activate_literals (solver, isize, ilits);
    if (!isize) {
#ifndef NDEBUG
      if (restore_check > 1)
        kissat_add_unchecked_external (solver, 0, 0);
#endif
      if (!solver->inconsistent) {
        solver->inconsistent = true;
        CHECK_AND_ADD_EMPTY ();
        ADD_EMPTY_TO_PROOF ();
      }
      res = 2;
    } else if (isize == 1) {
      const unsigned unit = TOP_STACK (solver->clause);
#ifndef NDEBUG
      if (restore_check > 1) {
        const int elit = kissat_export_literal (solver, unit);
        if (elit)
          kissat_add_unchecked_external (solver, 1, &elit);
      }
#endif
      kissat_learned_unit (solver, unit);
      if (!solver->level)
        (void) kissat_search_propagate (solver);
      res = 1;
    } else {
#ifndef NDEBUG
      if (restore_check > 1) {
        bool valid = true;
        int *elits =
            kissat_malloc (solver, isize * sizeof *elits);
        for (size_t i = 0; i < isize; i++) {
          const int elit = kissat_export_literal (solver, ilits[i]);
          if (!elit) {
            valid = false;
            break;
          }
          elits[i] = elit;
        }
        if (valid)
          kissat_add_unchecked_external (solver, isize, elits);
        kissat_free (solver, elits, isize * sizeof *elits);
      }
#endif
      (void) kissat_new_redundant_clause (solver, glue);
      res = 1;
    }
  }

DONE:
  for (all_stack (unsigned, lit, solver->clause))
    MARK (lit) = MARK (NOT (lit)) = 0;

  CLEAR_STACK (solver->clause);

  solver->clause_satisfied = false;
  solver->clause_trivial = false;
  solver->clause_shrink = false;

#if !defined(NDEBUG) && !defined(NOPTIONS)
  if (restore_check > 1)
    (void) kissat_set_option (solver, "check", restore_check);
#endif

  return res;
}

int kissat_solve (kissat *solver) {
  kissat_require_initialized (solver);
  kissat_require (EMPTY_STACK (solver->clause),
                  "incomplete clause (terminating zero not added)");
  kissat_require (!GET (searches), "incremental solving not supported");
  return kissat_search (solver);
}

void kissat_terminate (kissat *solver) {
  kissat_require_initialized (solver);
  solver->termination.flagged = ~(unsigned) 0;
  assert (solver->termination.flagged);
}

void kissat_set_terminate (kissat *solver, void *state,
                           int (*terminate) (void *)) {
  solver->termination.terminate = 0;
  solver->termination.state = state;
  solver->termination.terminate = terminate;
}

int kissat_value (kissat *solver, int elit) {
  kissat_require_initialized (solver);
  kissat_require_valid_external_internal (elit);
  const unsigned eidx = ABS (elit);
  if (eidx >= SIZE_STACK (solver->import))
    return 0;
  const import *const import = &PEEK_STACK (solver->import, eidx);
  if (!import->imported)
    return 0;
  value tmp;
  if (import->eliminated) {
    if (!solver->extended && !EMPTY_STACK (solver->extend))
      kissat_extend (solver);
    const unsigned eliminated = import->lit;
    tmp = PEEK_STACK (solver->eliminated, eliminated);
  } else {
    const unsigned ilit = import->lit;
    tmp = VALUE (ilit);
  }
  if (!tmp)
    return 0;
  if (elit < 0)
    tmp = -tmp;
  return tmp < 0 ? -elit : elit;
}
