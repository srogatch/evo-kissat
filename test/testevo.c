#include "test.h"

#include "../src/import.h"
#include "../src/literal.h"

#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static int run_evo_kissat (const char *const *args) {
  const char *path = args[0];

  pid_t child = fork ();
  if (child < 0)
    FATAL ("failed to fork evo-kissat");
  if (!child) {
    execv (path, (char *const *) args);
    _exit (1);
  }

  int wstatus = 0;
  pid_t pid = waitpid (child, &wstatus, 0);
  if (pid != child)
    FATAL ("failed to wait for evo-kissat");
  if (WIFSIGNALED (wstatus)) {
    const int sig = WTERMSIG (wstatus);
    FATAL ("evo-kissat terminated by signal %d", sig);
  }
  if (!WIFEXITED (wstatus))
    FATAL ("evo-kissat did not exit normally");

  const int status = WEXITSTATUS (wstatus);
  return status;
}

static char *write_temp_dimacs (const char *dimacs) {
  char template[] = "./testevo-invalid-literal-XXXXXX";
  const int fd = mkstemp (template);
  if (fd < 0)
    FATAL ("failed to create temporary DIMACS file");

  FILE *tmp = fdopen (fd, "w");
  if (!tmp) {
    close (fd);
    unlink (template);
    FATAL ("failed to open temporary DIMACS stream");
  }

  const int put_res = fputs (dimacs, tmp);
  const int close_res = fclose (tmp);
  if (put_res == EOF || close_res) {
    unlink (template);
    FATAL ("failed to write temporary DIMACS content");
  }

  char *res = malloc (strlen (template) + 1);
  if (!res) {
    unlink (template);
    FATAL ("failed to allocate temporary DIMACS path");
  }
  strcpy (res, template);
  return res;
}

static void test_evo_kissat_f2000 (void) {
  const char *cnf = "../test/cnf/f2000.cnf";
  const char *args[] = {
      "./evo-kissat",
      "-q",
      "--time=3",
      "--evo-evals=32",
      "--evo-pop=16",
      "--evo-threads=4",
      "--evo-eval-time=0.1",
      "--conflicts=500",
      cnf,
      0,
  };

  const int status = run_evo_kissat (args);
  if (status != 0 && status != 10 && status != 20)
    FATAL ("unexpected exit status %d from evo-kissat", status);
}

static void test_evo_kissat_rejects_large_literals (void) {
  // These malformed literals used to pass parsing and crash later in
  // kissat_add/kissat_reserve instead of failing as a parse error.
  const unsigned out_of_range = (unsigned) EXTERNAL_MAX_VAR + 1u;
  char dimacs[128];
  sprintf (dimacs, "p cnf 1 1\n%u 0\n", out_of_range);

  char *path = write_temp_dimacs (dimacs);
  const char *args[] = {"./evo-kissat", "-q", path, 0};
  const int status = run_evo_kissat (args);
  unlink (path);
  free (path);

  if (status != 1)
    FATAL ("expected parse failure for out-of-range literal, got %d", status);
}

static void test_evo_kissat_rejects_overflowing_literals (void) {
  char *path = write_temp_dimacs ("p cnf 1 1\n2147483648 0\n");
  const char *args[] = {"./evo-kissat", "-q", path, 0};
  const int status = run_evo_kissat (args);
  unlink (path);
  free (path);

  if (status != 1)
    FATAL ("expected parse failure for overflowing literal, got %d", status);
}

typedef struct shared_export_stats shared_export_stats;

struct shared_export_stats {
  int extension_var;
  unsigned binaries;
  bool saw_extension_literal;
};

static int shared_export_consumer (void *state, unsigned size, unsigned glue,
                                   const int *lits) {
  (void) glue;
  shared_export_stats *stats = state;
  if (size == 2)
    stats->binaries++;
  for (unsigned i = 0; i < size; i++)
    if (ABS (lits[i]) == stats->extension_var)
      stats->saw_extension_literal = true;
  return 0;
}

static void test_shared_export_skips_extension_literals (void) {
  kissat *solver = kissat_init ();
  tissat_init_solver (solver);

  kissat_reserve (solver, 2);
  kissat_add (solver, 1);
  kissat_add (solver, 2);
  kissat_add (solver, 0);

  const unsigned extension_lit = kissat_fresh_literal (solver);
  const int extension_elit = kissat_export_literal (solver, extension_lit);
  assert (extension_elit);

  const int original_binary[2] = {1, 2};
  if (kissat_import_shared_clause (solver, 2, original_binary, 1) != 1)
    FATAL ("expected original binary to be imported");

  const int extension_binary[2] = {1, extension_elit};
  if (kissat_import_shared_clause (solver, 2, extension_binary, 1) != 1)
    FATAL ("expected extension binary to be imported locally");

  const int extension_large[3] = {1, 2, extension_elit};
  if (kissat_import_shared_clause (solver, 3, extension_large, 1) != 1)
    FATAL ("expected extension large clause to be imported locally");

  shared_export_stats stats;
  memset (&stats, 0, sizeof stats);
  stats.extension_var = ABS (extension_elit);
  kissat_export_shared_clauses (solver, 12, 10, 1000, &stats,
                                shared_export_consumer);

  if (!stats.binaries)
    FATAL ("expected at least one shareable original binary clause");
  if (stats.saw_extension_literal)
    FATAL ("shared export leaked solver-local extension literal %d",
           extension_elit);

  kissat_release (solver);
}

void tissat_schedule_evo (void) {
  SCHEDULE_FUNCTION (test_evo_kissat_f2000);
  SCHEDULE_FUNCTION (test_evo_kissat_rejects_large_literals);
  SCHEDULE_FUNCTION (test_evo_kissat_rejects_overflowing_literals);
  SCHEDULE_FUNCTION (test_shared_export_skips_extension_literals);
}
